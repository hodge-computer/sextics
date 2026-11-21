import Proposal.GeometricMarkedEquationCharts
import Mathlib.LinearAlgebra.Determinant
import Mathlib.RingTheory.Noetherian.Orzech
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.FiniteType
import Proposal.GeometricMonicGenericSupport
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.Topology.Sheaves.Stalks

/-! Conormal generators and exact stalk frames. Differential bases adapted to prescribed equations descend to affine neighborhoods.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false

noncomputable section

namespace CycleQ2ConormalGeneratorChange

open Algebra Module

variable {A B M : Type} [CommRing A] [CommRing B] [AddCommGroup M] [Module B M]

theorem isUnit_det_of_spanning (φ : A →+* B) [IsLocalHom φ] [IsNoetherianRing B]
    {n : ℕ} (b : Basis (Fin n) B M) (x y : Fin n → M)
    (hx : Submodule.span B (Set.range x) = ⊤) (hy : Submodule.span B (Set.range y) = ⊤)
    (P : Matrix (Fin n) (Fin n) A) (hp : ∀ j, y j = ∑ i, φ (P i j) • x i) :
    IsUnit P.det := by
  let f := b.constr B x
  let g := b.constr B y
  let T := Matrix.toLin b b (P.map φ)
  let : Module.Finite B M := Module.Finite.of_basis b
  let : IsNoetherian B M := inferInstance
  have hf : Function.Surjective f := LinearMap.range_eq_top.mp ((b.constr_range B).trans hx)
  have hg : Function.Surjective g := LinearMap.range_eq_top.mp ((b.constr_range B).trans hy)
  have hi : Function.Injective f := IsNoetherian.injective_of_surjective_endomorphism f hf
  have hcomp : f.comp T = g := by
    apply b.ext
    intro j
    change f (Matrix.toLin b b (P.map φ) (b j)) = g (b j)
    rw [Matrix.toLin_self,map_sum]
    simp only [Matrix.map_apply,LinearMap.map_smul,f,g,Basis.constr_basis]
    exact (hp j).symm
  have ht : Function.Surjective T := by
    intro t
    obtain ⟨u,hu⟩ := hg (f t)
    exact ⟨u,hi ((LinearMap.congr_fun hcomp u).trans hu)⟩
  let e := LinearEquiv.ofBijective T ⟨IsNoetherian.injective_of_surjective_endomorphism T ht,ht⟩
  have he := e.isUnit_det b b
  change IsUnit (LinearMap.toMatrix b b (Matrix.toLin b b (P.map φ))).det at he
  rw [LinearMap.toMatrix_toLin] at he
  change IsUnit (φ.mapMatrix P).det at he
  rw [← φ.map_det] at he
  exact (isUnit_map_iff φ P.det).mp he

variable {k C : Type} [CommRing k] [CommRing C] [Algebra k C]
  (P : Extension k C) {n : ℕ}

/-- Any actual generating family of the kernel spans the actual conormal quotient. -/
theorem conormal_span (u : Fin n → P.ker)
    (hu : Ideal.span (Set.range (Subtype.val ∘ u)) = P.ker) :
    Submodule.span C (Set.range (Extension.Cotangent.mk (P := P) ∘ u)) = ⊤ := by
  let I := P.ker
  let M := Submodule.span P.Ring (Set.range u)
  have hm : M = ⊤ := by
    apply Submodule.map_injective_of_injective (Submodule.injective_subtype I)
    change (Submodule.span P.Ring (Set.range u)).map I.subtype = (⊤ : Submodule P.Ring I).map I.subtype
    rw [Submodule.map_span,← Set.range_comp,Submodule.map_top,Submodule.range_subtype]
    exact hu
  have he : M.map (Extension.Cotangent.mk (P := P)) = ⊤ := by
    rw [hm,Submodule.map_top,LinearMap.range_eq_top]
    exact Extension.Cotangent.mk_surjective
  rw [← Submodule.restrictScalars_inj (S := P.Ring) (R := C),
    Submodule.restrictScalars_top,Submodule.restrictScalars_span P.Ring C P.algebraMap_surjective,
    Set.range_comp,← Submodule.map_span]
  exact he

end CycleQ2ConormalGeneratorChange

namespace CycleQ2SmoothKernelGeneratorChange

open Algebra KaehlerDifferential Module
open CycleQ2SmoothConormalRank (presentation conormalBasis)
open CycleQ2ConormalGeneratorChange (conormal_span isUnit_det_of_spanning)

variable {k A B : Type} [CommRing k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
  [FormallySmooth k A] [FormallySmooth k B] [IsLocalRing B] [IsNoetherianRing B]
  (φ : A →ₐ[k] B) [IsLocalHom φ.toRingHom] (hφ : Function.Surjective φ)

include hφ in
theorem determinant_unit {n m : ℕ} (b : Basis (Fin n) A Ω[A⁄k]) (c : Basis (Fin m) B Ω[B⁄k])
    (f g : Fin (n-m) → A) (hf : Ideal.span (Set.range f) = RingHom.ker φ.toRingHom)
    (hg : Ideal.span (Set.range g) = RingHom.ker φ.toRingHom)
    (T : Matrix (Fin (n-m)) (Fin (n-m)) A) (hT : ∀ j, g j = ∑ i, T i j * f i) :
    IsUnit T.det := by
  let P := presentation φ hφ
  let x : Fin (n-m) → P.ker := fun i ↦ ⟨f i,by
    change f i ∈ RingHom.ker φ.toRingHom
    rw [← hf]
    exact Ideal.subset_span ⟨i,rfl⟩⟩
  let y : Fin (n-m) → P.ker := fun i ↦ ⟨g i,by
    change g i ∈ RingHom.ker φ.toRingHom
    rw [← hg]
    exact Ideal.subset_span ⟨i,rfl⟩⟩
  let TP : Fin (n-m) → Fin (n-m) → P.Ring := fun i j ↦ T i j
  let e := conormalBasis φ hφ b c
  let mk := Extension.Cotangent.mk (P := P)
  have hx : Submodule.span B (Set.range (mk ∘ x)) = ⊤ := conormal_span P x hf
  have hy : Submodule.span B (Set.range (mk ∘ y)) = ⊤ := conormal_span P y hg
  apply isUnit_det_of_spanning φ.toRingHom e _ _ hx hy T
  intro j
  have hxy : y j = ∑ i, TP i j • x i := by
    apply Subtype.ext
    simp only [Submodule.coe_sum,Submodule.coe_smul,smul_eq_mul]
    change g j = ∑ i, T i j * f i
    exact hT j
  change mk (y j) = ∑ i, φ (T i j) • mk (x i)
  rw [hxy,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul]
  change TP i j • mk (x i) = (algebraMap P.Ring B (TP i j)) • mk (x i)
  exact (algebraMap_smul P.Ring (TP i j) (mk (x i))).symm

end CycleQ2SmoothKernelGeneratorChange

namespace CycleQ2SmoothStalkGeneratorChange

open CategoryTheory AlgebraicGeometry Algebra
open CycleQ2SmoothStalkFrames (coefficientAlg exists_exact_frame formallySmooth_stalk)
open CycleQ2SmoothImmersionStalkEquations (stalkAlgHom)

variable {k : Type} [Field k] {X Y : Scheme.{0}}
  (p : X ⟶ Spec (CommRingCat.of k)) (q : Y ⟶ Spec (CommRingCat.of k))
  (i : X ⟶ Y) (hi : i ≫ q = p) (x : X)

include hi in
theorem determinant_unit (n m : ℕ) [SmoothOfRelativeDimension n q] [SmoothOfRelativeDimension m p]
    (hs : Function.Surjective (i.stalkMap x))
    (f g : Fin (n-m) → Y.presheaf.stalk (i x))
    (hf : Ideal.span (Set.range f) = RingHom.ker (i.stalkMap x).hom)
    (hg : Ideal.span (Set.range g) = RingHom.ker (i.stalkMap x).hom)
    (T : Matrix (Fin (n-m)) (Fin (n-m)) (Y.presheaf.stalk (i x)))
    (hT : ∀ j, g j = ∑ l, T l j * f l) : IsUnit T.det := by
  letI : Smooth q := SmoothOfRelativeDimension.smooth n q
  letI : Smooth p := SmoothOfRelativeDimension.smooth m p
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  letI := coefficientAlg q (i x)
  letI := coefficientAlg p x
  letI : FormallySmooth k (Y.presheaf.stalk (i x)) := formallySmooth_stalk q (i x)
  letI : FormallySmooth k (X.presheaf.stalk x) := formallySmooth_stalk p x
  let φ := stalkAlgHom p q i hi x
  letI : IsLocalHom φ.toRingHom := inferInstanceAs (IsLocalHom (i.stalkMap x).hom)
  obtain ⟨_,b,_⟩ := exists_exact_frame q (i x) n
  obtain ⟨_,c,_⟩ := exists_exact_frame p x m
  exact CycleQ2SmoothKernelGeneratorChange.determinant_unit φ hs b c f g hf hg T hT

end CycleQ2SmoothStalkGeneratorChange

namespace CycleQ2AffineEquationGerms

open CategoryTheory AlgebraicGeometry

variable {X Y : Scheme.{0}} (i : X ⟶ Y) [IsClosedImmersion i] (U : Y.affineOpens)
  (x : X) (hx : i x ∈ U.1)

theorem span_pair (f g : Γ(Y,U.1)) (hf : Ideal.span {f,g} = i.ker.ideal U) :
    let ρ := (Y.presheaf.germ U.1 (i x) hx).hom
    Ideal.span (Set.range ![ρ f,ρ g]) = RingHom.ker (i.stalkMap x).hom := by
  let ρ := (Y.presheaf.germ U.1 (i x) hx).hom
  have hpair : ∀ {R : Type} (u v : R), Set.range ![u,v] = {u,v} := by
    intro R u v
    ext z
    constructor
    · rintro ⟨j,rfl⟩
      fin_cases j <;> simp
    · intro h
      rcases (show z = u ∨ z = v from h) with rfl | rfl
      · exact ⟨0,rfl⟩
      · exact ⟨1,rfl⟩
  change Ideal.span (Set.range ![ρ f,ρ g]) = _
  rw [hpair (ρ f) (ρ g),← CycleQ2ClosedImmersionStalkIdeal.map_kernel i U.1 U.2 x hx, ← i.ker_apply U,
    ← hf,Ideal.map_span,Set.image_pair]

end CycleQ2AffineEquationGerms

namespace CycleQ2SmoothAffineGeneratorChange

open CategoryTheory AlgebraicGeometry

variable {k : Type} [Field k] {X Y : Scheme.{0}}
  (p : X ⟶ Spec (CommRingCat.of k)) (q : Y ⟶ Spec (CommRingCat.of k))
  (i : X ⟶ Y) [IsClosedImmersion i] (hi : i ≫ q = p)
  [SmoothOfRelativeDimension 2 p] [SmoothOfRelativeDimension 4 q]

private theorem pair_change {R L : Type} [CommRing R] [CommRing L]
    (ρ : R →+* L) (a b c d f g f' g' : R) (hf : a*f+b*g = f') (hg : c*f+d*g = g') :
    ∀ j : Fin 2, (![ρ f',ρ g'] : Fin 2 → L) j =
      ∑ l, (!![ρ a,ρ c;ρ b,ρ d] : Matrix (Fin 2) (Fin 2) L) l j * (![ρ f,ρ g] : Fin 2 → L) l := by
  intro j
  fin_cases j <;> simp [Fin.sum_univ_two,← map_mul,← map_add,hf,hg]

private theorem pair_det {R L : Type} [CommRing R] [CommRing L] (ρ : R →+* L) (a b c d : R) :
    (!![ρ a,ρ c;ρ b,ρ d] : Matrix (Fin 2) (Fin 2) L).det = ρ (a*d-b*c) := by
  simp [Matrix.det_fin_two,map_sub,map_mul,mul_comm]

include hi in
theorem exists_matrix (U : Y.affineOpens) (x : X) (hx : i x ∈ U.1)
    (f g f' g' : Γ(Y,U.1)) (hf : Ideal.span {f,g} = i.ker.ideal U)
    (hg : Ideal.span {f',g'} = i.ker.ideal U) :
    ∃ a b c d : Γ(Y,U.1), f' = a*f+b*g ∧ g' = c*f+d*g ∧ i x ∈ Y.basicOpen (a*d-b*c) := by
  have hp : f' ∈ Ideal.span {f,g} := by
    rw [hf,← hg]
    exact Ideal.subset_span (Set.mem_insert _ _)
  have hq : g' ∈ Ideal.span {f,g} := by
    rw [hf,← hg]
    exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  obtain ⟨a,b,ha⟩ := Ideal.mem_span_pair.mp hp
  obtain ⟨c,d,hc⟩ := Ideal.mem_span_pair.mp hq
  let ρ := (Y.presheaf.germ U.1 (i x) hx).hom
  let T : Matrix (Fin 2) (Fin 2) (Y.presheaf.stalk (i x)) := !![ρ a,ρ c;ρ b,ρ d]
  have hr := pair_change ρ a b c d f g f' g' ha hc
  have ht := CycleQ2SmoothStalkGeneratorChange.determinant_unit p q i hi x 4 2
    (i.stalkMap_surjective x) ![ρ f,ρ g] ![ρ f',ρ g'] (CycleQ2AffineEquationGerms.span_pair i U x hx f g hf)
    (CycleQ2AffineEquationGerms.span_pair i U x hx f' g' hg) T hr
  refine ⟨a,b,c,d,ha.symm,hc.symm,(Y.mem_basicOpen _ (i x) hx).mpr ?_⟩
  change IsUnit (ρ (a*d-b*c))
  rw [← pair_det ρ a b c d]
  exact ht

end CycleQ2SmoothAffineGeneratorChange

namespace CycleQ2NormalTangentFrame

open Algebra Module KaehlerDifferential
open scoped TensorProduct
open CycleQ2SmoothConormalRank (presentation)
open CycleQ2ConormalGeneratorChange (conormal_span)

variable {k A B : Type} [CommRing k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]

/-- The differentials of a prescribed generating family of the ideal,
together with lifts of coordinates on the closed subscheme, span the
restriction of the ambient differential module to that subscheme. -/
theorem span_after_restriction (φ : A →ₐ[k] B) (hφ : Function.Surjective φ)
    {n m : ℕ} (f : Fin n → A) (hf : Ideal.span (Set.range f) = RingHom.ker φ.toRingHom)
    (u : Fin m → A) (c : Basis (Fin m) B Ω[B⁄k]) (hc : ∀ j, c j = D k B (φ (u j))) :
    letI : Algebra A B := φ.toAlgebra
    Submodule.span B (Set.range (fun j => (1:B) ⊗ₜ[A] D k A (Fin.append f u j))) = ⊤ := by
  letI : Algebra A B := φ.toAlgebra
  let P := presentation φ hφ
  let f' : Fin n → P.ker := fun j => ⟨f j, by
    change f j ∈ RingHom.ker φ.toRingHom
    rw [← hf]
    exact Ideal.subset_span ⟨j,rfl⟩⟩
  let v (j : Fin (n+m)) : B ⊗[A] Ω[A⁄k] := (1:B) ⊗ₜ[A] D k A (Fin.append f u j)
  let L := Submodule.span B (Set.range v)
  change L = ⊤
  have hker : LinearMap.ker P.toKaehler ≤ L := by
    rw [LinearMap.exact_iff.mp P.exact_cotangentComplex_toKaehler,
      ← Submodule.map_top, ← conormal_span P f' hf, Submodule.map_span]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨_,⟨j,rfl⟩,rfl⟩
    apply Submodule.subset_span (R := B) (s := Set.range v)
    refine ⟨Fin.castAdd m j,?_⟩
    change (1:B) ⊗ₜ[A] D k A (Fin.append f u (Fin.castAdd m j)) =
      P.cotangentComplex (Extension.Cotangent.mk (f' j))
    rw [Fin.append_left,P.cotangentComplex_mk]
    rfl
  have htop : L.map P.toKaehler = ⊤ := by
    rw [_root_.eq_top_iff, ← c.span_eq, Submodule.span_le]
    rintro _ ⟨j,rfl⟩
    refine ⟨v (Fin.natAdd n j),Submodule.subset_span (R := B) (s := Set.range v) ⟨_,rfl⟩,?_⟩
    change mapBaseChange k A B ((1:B) ⊗ₜ[A] D k A (Fin.append f u (Fin.natAdd n j))) = c j
    rw [Fin.append_right, mapBaseChange_tmul, one_smul, map_D, hc] <;> rfl
  have hl := (Submodule.comap_map_eq P.toKaehler L).symm
  rw [htop, Submodule.comap_top, sup_eq_left.mpr hker] at hl
  exact hl

end CycleQ2NormalTangentFrame

namespace CycleQ2FrameLifting

open Module
open scoped TensorProduct

variable {A B M : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [IsLocalHom (algebraMap A B)] [AddCommGroup M] [Module A M] {n : ℕ}

/-- A list whose base change spans a free module of the same rank is already a
basis when the coefficient map reflects units. -/
theorem basis_of_baseChange_span (b : Basis (Fin n) A M) (v : Fin n → M)
    (hv : Submodule.span B (Set.range (fun j => (1 : B) ⊗ₜ[A] v j)) = ⊤) :
    ∃ b' : Basis (Fin n) A M, ∀ j, b' j = v j := by
  classical
  let f := b.constr A v
  let g := f.baseChange B
  let c := b.baseChange B
  let : Module.Free A M := Module.Free.of_basis b
  let : Module.Finite A M := Module.Finite.of_basis b
  let : Module.Finite B (B ⊗[A] M) := Module.Finite.of_basis c
  have he : g = c.constr B (fun j => (1 : B) ⊗ₜ[A] v j) := by
    apply c.ext
    intro j
    rw [Basis.constr_basis]
    change f.baseChange B ((b.baseChange B) j) = _
    rw [Basis.baseChange_apply,LinearMap.baseChange_tmul]
    exact congrArg (fun m => (1 : B) ⊗ₜ[A] m) (b.constr_basis A v j)
  have hg : Function.Surjective g := LinearMap.range_eq_top.mp (by rw [he,c.constr_range B,hv])
  have hd : IsUnit g.det :=
    LinearMap.isUnit_det g ((Module.End.isUnit_iff _).mpr
      (OrzechProperty.bijective_of_surjective_endomorphism g hg))
  change IsUnit (f.baseChange B).det at hd
  rw [LinearMap.det_baseChange,isUnit_map_iff] at hd
  refine ⟨b.map (LinearMap.equivOfIsUnitDet hd), fun j => ?_⟩
  simp [f]

end CycleQ2FrameLifting

namespace CycleQ2NormalTangentFrame

open CategoryTheory AlgebraicGeometry Algebra Module KaehlerDifferential
open CycleQ2SmoothStalkFrames (coefficientAlg exists_exact_frame)
open CycleQ2SmoothImmersionStalkEquations (stalkAlgHom)
open scoped TensorProduct

variable {k : Type} [Field k] {X Y : Scheme.{0}}
  (p : X ⟶ Spec (CommRingCat.of k)) (q : Y ⟶ Spec (CommRingCat.of k))
  (i : X ⟶ Y) [IsClosedImmersion i] (hi : i ≫ q = p)
  {n m : ℕ} [SmoothOfRelativeDimension m p] [SmoothOfRelativeDimension (n+m) q]

include hi in
theorem stalk_basis (x : X) (f : Fin n → Y.presheaf.stalk (i x))
    (hf : Ideal.span (Set.range f) = RingHom.ker (i.stalkMap x).hom) :
    letI := coefficientAlg q (i x)
    letI := coefficientAlg p x
    ∃ (u : Fin m → Y.presheaf.stalk (i x))
      (b : Basis (Fin (n+m)) (Y.presheaf.stalk (i x)) Ω[Y.presheaf.stalk (i x)⁄k])
      (c : Basis (Fin m) (X.presheaf.stalk x) Ω[X.presheaf.stalk x⁄k]),
      (∀ j, b j = D k _ (Fin.append f u j)) ∧
        ∀ j, c j = D k _ ((i.stalkMap x) (u j)) := by
  letI := coefficientAlg q (i x)
  letI := coefficientAlg p x
  let φ := stalkAlgHom p q i hi x
  letI : Algebra (Y.presheaf.stalk (i x)) (X.presheaf.stalk x) := φ.toAlgebra
  let : IsLocalHom (algebraMap (Y.presheaf.stalk (i x)) (X.presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom (i.stalkMap x).hom)
  obtain ⟨_,b,_⟩ := exists_exact_frame q (i x) (n+m)
  obtain ⟨v,c,hv⟩ := exists_exact_frame p x m
  choose u hu using fun j => i.stalkMap_surjective x (v j)
  have hc (j : Fin m) : c j = D k _ (φ (u j)) := by
    rw [hv]
    exact congrArg (D k _) (hu j).symm
  obtain ⟨b',hb'⟩ := CycleQ2FrameLifting.basis_of_baseChange_span
    (B := X.presheaf.stalk x) b (fun j => D k _ (Fin.append f u j))
    (span_after_restriction φ (i.stalkMap_surjective x) f hf u c hc)
  exact ⟨u,b',c,hb',hc⟩

end CycleQ2NormalTangentFrame

namespace CycleQ2BaseChangeJacobian

open KaehlerDifferential Module
open CycleQ2RelativeAffineOverlap (baseChangeFrame)

variable {K A B : Type} [CommRing K] [CommRing A] [Algebra K A]
  {n : ℕ} (b : Basis (Fin n) A Ω[A⁄K]) (v : Fin n → A)

def jacobian : A := b.det (fun j => D K A (v j))

theorem frame_iff_unit :
    (∃ c : Basis (Fin n) A Ω[A⁄K], ∀ j, c j = D K A (v j)) ↔ IsUnit (jacobian b v) := by
  constructor
  · rintro ⟨c,hc⟩
    change IsUnit (b.det (fun j => D K A (v j)))
    rw [← (funext hc : ⇑c = fun j => D K A (v j))]
    exact b.isUnit_det c
  · intro h
    obtain ⟨hi,hs⟩ := b.is_basis_iff_det.mpr h
    exact ⟨Basis.mk hi hs.ge, fun j => Basis.mk_apply _ _ _⟩

variable [CommRing B] [Algebra K B] [Algebra A B] [IsScalarTower K A B]
  [Algebra.FormallyEtale A B]

theorem map_matrix :
    (algebraMap A B).mapMatrix (b.toMatrix (fun j => D K A (v j))) =
    (baseChangeFrame b).toMatrix (fun j => D K B (algebraMap A B (v j))) := by
  ext i j
  simp [RingHom.mapMatrix_apply, Basis.toMatrix_apply, CycleQ2RelativeAffineOverlap.baseChangeFrame,
    tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap, Algebra.smul_def]

theorem map_jacobian :
    algebraMap A B (jacobian b v) =
      jacobian (baseChangeFrame b) (fun j => algebraMap A B (v j)) := by
  unfold jacobian
  rw [Basis.det_apply,Basis.det_apply,(algebraMap A B).map_det,map_matrix b v]

end CycleQ2BaseChangeJacobian

section
namespace CycleQ2AffineStalkRepresentatives

open AlgebraicGeometry CategoryTheory TopologicalSpace

theorem exists_lifts (X : Scheme.{0}) (U : X.Opens) (x : X) (hx : x ∈ U)
    {n : ℕ} (z : Fin n → X.presheaf.stalk x) :
    ∃ (V : X.affineOpens) (h : V.1 ≤ U) (hxV : x ∈ V.1) (s : Fin n → Γ(X,V.1)),
      (∀ i, X.presheaf.germ V.1 x hxV (s i) = z i) ∧
        ∀ f : Γ(X,U), X.presheaf.germ V.1 x hxV (X.presheaf.map (homOfLE h).op f) =
          X.presheaf.germ U x hx f := by
  classical
  choose W hxW t ht using fun i => X.presheaf.exists_germ_eq (z i)
  let O : X.Opens := U ⊓ ⨅ i, W i
  have hxO : x ∈ O := by
    refine ⟨hx,?_⟩
    change x ∈ ((⨅ i, W i : X.Opens) : Set X)
    rw [Opens.coe_iInf]
    exact Set.mem_iInter.mpr hxW
  obtain ⟨V,hV,hxV,hVO⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hxO
  let h (i : Fin n) : V ≤ W i := (hVO.trans inf_le_right).trans (iInf_le _ i)
  refine ⟨⟨V,hV⟩,hVO.trans inf_le_left,hxV,fun i => X.presheaf.map (homOfLE (h i)).op (t i),?_,?_⟩
  · intro i
    exact (TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE (h i)) x hxV (t i)).trans (ht i)
  · intro f
    exact TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE (hVO.trans inf_le_left)) x hxV f

end CycleQ2AffineStalkRepresentatives
end

namespace CycleQ2AdaptedAffineFrame

open AlgebraicGeometry CategoryTheory TopologicalSpace Algebra KaehlerDifferential Module
open CycleQ2SmoothRelativeFrames (sectionCoefficients)
open CycleQ2SmoothStalkFrames (coefficientAlg coefficient_from_open)
open CycleQ2RelativeAffineOverlap (restrict restrict_etale baseChangeFrame)
open CycleQ2FiniteExactAffineAtlas (HasFrame hasFrame_of_affine_le)
open CycleQ2BaseChangeJacobian (jacobian map_jacobian frame_iff_unit)

variable {k : Type} [Field k] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k)) {n : ℕ}

def ExactOnOpen {U : X.Opens} (a : Fin n → Γ(X,U)) : Prop :=
  letI := (sectionCoefficients p U).toAlgebra
  ∃ b : Basis (Fin n) Γ(X,U) Ω[Γ(X,U)⁄k], ∀ j, b j = D k Γ(X,U) (a j)

def ExactAt (x : X) (a : Fin n → X.presheaf.stalk x) : Prop :=
  letI := coefficientAlg p x
  ∃ b : Basis (Fin n) (X.presheaf.stalk x) Ω[X.presheaf.stalk x⁄k],
    ∀ j, b j = D k (X.presheaf.stalk x) (a j)

/-- A tuple already defined on an affine open is a differential basis on
the principal open cut out by its Jacobian. -/
theorem shrink (U : X.affineOpens) (x : X) (hx : x ∈ U.1)
    (hu : HasFrame p n U.1) (a : Fin n → Γ(X,U.1))
    (ha : ExactAt p x (fun j => X.presheaf.germ U.1 x hx (a j))) :
    ∃ (V : X.affineOpens) (h : V.1 ≤ U.1), x ∈ V.1 ∧
      ExactOnOpen p (fun j => X.presheaf.map (homOfLE h).op (a j)) := by
  letI := (sectionCoefficients p U.1).toAlgebra
  letI := coefficientAlg p x
  letI : Algebra Γ(X,U.1) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x,hx⟩
  letI : IsScalarTower k Γ(X,U.1) (X.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_eq' (coefficient_from_open p x U.1 hx)
  let q := (U.2.primeIdealOf ⟨x,hx⟩).asIdeal
  let : q.IsPrime := (U.2.primeIdealOf ⟨x,hx⟩).isPrime
  let : IsLocalization.AtPrime (X.presheaf.stalk x) q := U.2.isLocalization_stalk ⟨x,hx⟩
  let : FormallyEtale Γ(X,U.1) (X.presheaf.stalk x) := FormallyEtale.of_isLocalization q.primeCompl
  obtain ⟨_,b,_⟩ := hu
  let δ := jacobian b a
  have hd : IsUnit (algebraMap Γ(X,U.1) (X.presheaf.stalk x) δ) := by
    change IsUnit (algebraMap _ _ (jacobian b a))
    rw [map_jacobian]
    exact (frame_iff_unit _ _).mp ha
  let V := X.affineBasicOpen δ
  have hi : V.1 ≤ U.1 := X.basicOpen_le δ
  refine ⟨V,hi,(X.mem_basicOpen δ x hx).mpr hd,?_⟩
  letI := (sectionCoefficients p V.1).toAlgebra
  letI : Algebra Γ(X,U.1) Γ(X,V.1) := (restrict p hi).toRingHom.toAlgebra
  letI : IsScalarTower k Γ(X,U.1) Γ(X,V.1) := IsScalarTower.of_algHom (restrict p hi)
  let : Algebra.Etale Γ(X,U.1) Γ(X,V.1) := (restrict_etale hi U.2 V.2).toAlgebra
  apply (frame_iff_unit (baseChangeFrame (B := Γ(X,V.1)) b)
    (fun j => algebraMap Γ(X,U.1) Γ(X,V.1) (a j))).mpr
  rw [← map_jacobian]
  exact X.toRingedSpace.isUnit_res_basicOpen δ

/-- Choose any subset of the coordinates to keep. Their affine representatives
are exactly the restrictions of the given sections. All the representatives
also realize the specified germs at the original point. -/
theorem exists_prescribed_frame (U : X.affineOpens) (x : X) (hx : x ∈ U.1)
    (hU : HasFrame p n U.1) (ur : Fin n → X.presheaf.stalk x)
    (fixed : Fin n → Γ(X,U.1)) (active : Set (Fin n))
    (hagree : ∀ j ∈ active, X.presheaf.germ U.1 x hx (fixed j) = ur j)
    (hstalk : ExactAt p x ur) :
    ∃ (V : X.affineOpens) (h : V.1 ≤ U.1) (hxV : x ∈ V.1) (w : Fin n → Γ(X,V.1)),
      ExactOnOpen p w ∧ (∀ j, X.presheaf.germ V.1 x hxV (w j) = ur j) ∧
        ∀ j ∈ active, w j = X.presheaf.map (homOfLE h).op (fixed j) := by
  classical
  obtain ⟨A,hA,hxA,l,hl,hw⟩ := CycleQ2AffineStalkRepresentatives.exists_lifts X U.1 x hx ur
  let a (j : Fin n) : Γ(X,A.1) :=
    if j ∈ active then X.presheaf.map (homOfLE hA).op (fixed j) else l j
  have hga : (fun j => X.presheaf.germ A.1 x hxA (a j)) = ur := by
    funext j
    by_cases hj : j ∈ active
    · simpa only [a,if_pos hj] using (hw (fixed j)).trans (hagree j hj)
    · simpa only [a,if_neg hj] using hl j
  obtain ⟨V,hV,hxV,hframe⟩ := shrink p A x hxA
    (hasFrame_of_affine_le p n hA U.2 A.2 hU) a (hga.symm ▸ hstalk)
  let w (j : Fin n) : Γ(X,V.1) := X.presheaf.map (homOfLE hV).op (a j)
  refine ⟨V,hV.trans hA,hxV,w,hframe,?_,?_⟩
  · intro j
    change X.presheaf.germ V.1 x hxV (X.presheaf.map (homOfLE hV).op (a j)) = ur j
    rw [X.presheaf.germ_res_apply]
    exact congrFun hga j
  · intro j hj
    change X.presheaf.map (homOfLE hV).op (a j) =
      X.presheaf.map (homOfLE (hV.trans hA)).op (fixed j)
    simp only [a,if_pos hj]
    change ((X.presheaf.map (homOfLE hA).op) ≫ (X.presheaf.map (homOfLE hV).op)) (fixed j) = _
    rw [← Functor.map_comp]
    rfl

/-- On a fourfold the first two coordinates can be prescribed functions on the
original chart. This keeps the two defining equations of a surface fixed. -/
theorem exists_pair_frame (U : X.affineOpens) (x : X) (hx : x ∈ U.1)
    (hU : HasFrame p 4 U.1) (f g : Γ(X,U.1)) (ur : Fin 4 → X.presheaf.stalk x)
    (hf : ur 0 = X.presheaf.germ U.1 x hx f)
    (hg : ur 1 = X.presheaf.germ U.1 x hx g) (hstalk : ExactAt p x ur) :
    ∃ (V : X.affineOpens) (h : V.1 ≤ U.1) (hxV : x ∈ V.1) (w : Fin 4 → Γ(X,V.1)),
      ExactOnOpen p w ∧ (∀ j, X.presheaf.germ V.1 x hxV (w j) = ur j) ∧
      w 0 = X.presheaf.map (homOfLE h).op f ∧ w 1 = X.presheaf.map (homOfLE h).op g := by
  let fixed : Fin 4 → Γ(X,U.1) := ![f,g,0,0]
  have hf0 : fixed 0 = f := rfl
  have hg1 : fixed 1 = g := rfl
  have agree (j : Fin 4) (hj : j ∈ ({0,1} : Set (Fin 4))) :
      X.presheaf.germ U.1 x hx (fixed j) = ur j := by
    rcases Set.mem_insert_iff.mp hj with h | h
    · subst j
      exact hf.symm
    · have he := Set.mem_singleton_iff.mp h
      subst j
      exact hg.symm
  obtain ⟨V,h,hxV,w,hw,hwg,hwf⟩ :=
    exists_prescribed_frame p U x hx hU ur fixed {0,1} agree hstalk
  exact ⟨V,h,hxV,w,hw,hwg,hwf 0 (by simp),hwf 1 (by simp)⟩

end CycleQ2AdaptedAffineFrame

section

end
