import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
import Mathlib.Tactic

/-! # Linear splittings, rank tests and Čech lifting relations -/

set_option Elab.async false

/- Component: continuation_3/LinearAnnihilatorKernel.lean -/
section
/-! Exactness forced by a small annihilator and dimension bounds. The proof
uses only the actual entry image, the full image, and the restricted detector.
No preselected entry correction or large invertible matrix is assumed.
-/

noncomputable section
set_option maxHeartbeats 300000

namespace CycleQ2LinearAnnihilatorKernel

variable {K V W X : Type*} [Field K]
  [AddCommGroup V] [Module K V] [Module.Finite K V]
  [AddCommGroup W] [Module K W] [AddCommGroup X] [Module K X]

theorem annihilator_kernel_eq_entry_range
    (E : W →ₗ[K] V) (J : X →ₗ[K] V) (r s : ℕ) (L : V →ₗ[K] (Fin s → K))
    (hEJ : LinearMap.range E≤LinearMap.range J)
    (hJ : Module.finrank K (LinearMap.range J)≤r+s)
    (hE : r≤Module.finrank K (LinearMap.range E))
    (hLE : L.comp E=0)
    (hsurj : Function.Surjective (L.domRestrict (LinearMap.range J))) :
    LinearMap.range J ⊓ LinearMap.ker L=LinearMap.range E := by
  let U : Submodule K V := LinearMap.range J
  let P : Submodule K U := (LinearMap.range E).comap U.subtype
  let T : U →ₗ[K] (Fin s → K) := L.domRestrict U
  have hPK : P≤LinearMap.ker T := by
    intro y hy
    change (y:V)∈LinearMap.range E at hy
    obtain ⟨w,hw⟩ := hy
    change L (y:V)=0
    rw [←hw]
    exact LinearMap.congr_fun hLE w
  have hPdim : Module.finrank K P=Module.finrank K (LinearMap.range E) :=
    (Submodule.comapSubtypeEquivOfLe hEJ).finrank_eq
  have hPbound : r≤Module.finrank K P := by
    rw [hPdim]
    exact hE
  have hTsurj : Function.Surjective T := hsurj
  have hTdim : Module.finrank K (LinearMap.range T)=s := by
    rw [LinearMap.range_eq_top.mpr hTsurj]
    simp only [finrank_top,Module.finrank_fintype_fun_eq_card,Fintype.card_fin]
  have hUbound : Module.finrank K U≤r+s := hJ
  have hnull := T.finrank_range_add_finrank_ker
  rw [hTdim] at hnull
  have hKbound : Module.finrank K (LinearMap.ker T)≤r := by omega
  have heq : P=LinearMap.ker T :=
    Submodule.eq_of_le_of_finrank_eq hPK
      (Nat.le_antisymm (Submodule.finrank_mono hPK) (hKbound.trans hPbound))
  ext y
  constructor
  · intro hy
    let q : U := ⟨y,hy.1⟩
    have hq : q∈LinearMap.ker T := by
      change L y=0
      exact hy.2
    have hp : q∈P := by rw [heq]; exact hq
    change y∈LinearMap.range E at hp
    exact hp
  · intro hy
    refine ⟨hEJ hy,?_⟩
    obtain ⟨w,rfl⟩ := hy
    change L (E w)=0
    exact LinearMap.congr_fun hLE w

theorem exists_entry_correction
    (E : W →ₗ[K] V) (J : X →ₗ[K] V) (r s : ℕ) (L : V →ₗ[K] (Fin s → K))
    (hEJ : LinearMap.range E≤LinearMap.range J)
    (hJ : Module.finrank K (LinearMap.range J)≤r+s)
    (hE : r≤Module.finrank K (LinearMap.range E))
    (hLE : L.comp E=0)
    (hsurj : Function.Surjective (L.domRestrict (LinearMap.range J)))
    (y : V) (hy : y∈LinearMap.range J) (hLy : L y=0) :
    ∃ w : W, E w=y := by
  change y∈LinearMap.range E
  rw [←annihilator_kernel_eq_entry_range E J r s L hEJ hJ hE hLE hsurj]
  exact ⟨hy,hLy⟩

end CycleQ2LinearAnnihilatorKernel

#print axioms CycleQ2LinearAnnihilatorKernel.annihilator_kernel_eq_entry_range
#print axioms CycleQ2LinearAnnihilatorKernel.exists_entry_correction
end
end

/- Component: continuation_3/LinearAnnihilatorRank.lean -/
section
/-! # Rank gained by directions detected by an annihilator of an existing image -/

noncomputable section
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CycleQ2LinearAnnihilatorRank

variable {K X Z V Y W : Type*} [Field K]
  [AddCommGroup X] [Module K X] [AddCommGroup Z] [Module K Z]
  [AddCommGroup V] [Module K V] [AddCommGroup Y] [Module K Y]
  [AddCommGroup W] [Module K W] [FiniteDimensional K Y]

/-- The old image lies in the kernel of the restricted detector, while the
new detected image lies in its range. Rank-nullity gives the sum bound. -/
theorem rank_add_le_of_annihilator (f : X →ₗ[K] Y) (g : Z →ₗ[K] Y)
    (H : V →ₗ[K] Y) (L : Y →ₗ[K] W)
    (hf : LinearMap.range f≤LinearMap.range H)
    (hg : LinearMap.range g≤LinearMap.range H) (hLf : L.comp f=0) :
    Module.finrank K (LinearMap.range f)+Module.finrank K (LinearMap.range (L.comp g))≤
      Module.finrank K (LinearMap.range H) := by
  let R := LinearMap.range H
  let T : R →ₗ[K] W := L.comp R.subtype
  have hzero (y : LinearMap.range f) : L y.val=0 := by
    obtain ⟨x,hx⟩ := y.property
    rw [←hx]
    exact LinearMap.congr_fun hLf x
  let inclusion : LinearMap.range f →ₗ[K] LinearMap.ker T :=
    { toFun := fun y => ⟨⟨y.val,hf y.property⟩,hzero y⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : Function.Injective inclusion := by
    intro a b hab
    apply Subtype.ext
    exact congrArg (fun y : LinearMap.ker T => y.val.val) hab
  have h1 : Module.finrank K (LinearMap.range f)≤Module.finrank K (LinearMap.ker T) :=
    LinearMap.finrank_le_finrank_of_injective hinj
  have h2 : LinearMap.range (L.comp g)≤LinearMap.range T := by
    rintro z ⟨x,rfl⟩
    exact ⟨⟨g x,hg ⟨x,rfl⟩⟩,rfl⟩
  have h3 := Submodule.finrank_mono h2
  have h4 := T.finrank_range_add_finrank_ker
  change Module.finrank K (LinearMap.range T)+Module.finrank K (LinearMap.ker T)=
    Module.finrank K (LinearMap.range H) at h4
  omega

variable {m n a b k : Type*} [Fintype m] [Fintype n] [Fintype a] [Fintype b] [Fintype k]

theorem selected_columns_range_le (H : Matrix m n K) (c : a → n) :
    LinearMap.range (Matrix.mulVecLin (H.submatrix id c))≤
      LinearMap.range (Matrix.mulVecLin H) := by
  rw [Matrix.range_mulVecLin,Matrix.range_mulVecLin]
  apply Submodule.span_mono
  rintro _ ⟨j,rfl⟩
  exact ⟨c j,rfl⟩

/-- A checked left-annihilator of one selected column block detects new
independent columns without any assumption about an unchecked large minor. -/
theorem selected_column_rank_add_le (H : Matrix m n K) (c0 : a → n) (c1 : b → n)
    (L : Matrix k m K) (hL : L*H.submatrix id c0=0) :
    (H.submatrix id c0).rank+(L*H.submatrix id c1).rank≤H.rank := by
  simp only [Matrix.rank]
  rw [Matrix.mulVecLin_mul L (H.submatrix id c1)]
  apply rank_add_le_of_annihilator (Matrix.mulVecLin (H.submatrix id c0))
    (Matrix.mulVecLin (H.submatrix id c1)) (Matrix.mulVecLin H) (Matrix.mulVecLin L)
    (selected_columns_range_le H c0) (selected_columns_range_le H c1)
  rw [←Matrix.mulVecLin_mul,hL]
  ext x
  simp

end CycleQ2LinearAnnihilatorRank

#print axioms CycleQ2LinearAnnihilatorRank.rank_add_le_of_annihilator
#print axioms CycleQ2LinearAnnihilatorRank.selected_column_rank_add_le
end
end

/- Component: continuation_3/LinearExactSequenceSplit.lean -/
section
/-! # Compatible nonconstructive coordinates for an exact Jacobian sequence

The equation space is split into the image of the Jacobian and a complement
detected by the actual relation matrix.  Both square seed blocks become the
identity in these coordinates.  The coordinate changes are selected from
proved exactness; no numerical pivot or inverse is an extra premise.
-/

noncomputable section
set_option maxHeartbeats 600000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CycleQ2LinearExactSequenceSplit

open Matrix

variable {K X Y Z : Type*} [Field K]
  [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]
  [AddCommGroup Z] [Module K Z]

/-- A compatible splitting, including an extension of the relation-coordinate
projection from the actual image to the whole relation space. -/
theorem exists_split (f : X →ₗ[K] Y) (g : Y →ₗ[K] Z)
    (hexact : LinearMap.range f = LinearMap.ker g) :
    ∃ (B : LinearMap.ker g →ₗ[K] X)
      (S : LinearMap.range g →ₗ[K] Y)
      (P : Y →ₗ[K] LinearMap.ker g)
      (T : Z →ₗ[K] LinearMap.range g),
      f.comp B = (LinearMap.ker g).subtype ∧
      g.rangeRestrict.comp S = LinearMap.id ∧
      (LinearMap.ker g).subtype.comp P + S.comp g.rangeRestrict = LinearMap.id ∧
      P.comp (LinearMap.ker g).subtype = LinearMap.id ∧
      P.comp S = 0 ∧
      T.comp (LinearMap.range g).subtype = LinearMap.id := by
  let f' : X →ₗ[K] LinearMap.ker g :=
    f.codRestrict (LinearMap.ker g) (fun x => hexact ▸ LinearMap.mem_range_self f x)
  have hf' : Function.Surjective f' := by
    intro y
    obtain ⟨x,hx⟩ := (show y.val ∈ LinearMap.range f from hexact.symm ▸ y.property)
    exact ⟨x,Subtype.ext hx⟩
  obtain ⟨B,hB⟩ := f'.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hf')
  obtain ⟨S,hS⟩ := g.rangeRestrict.exists_rightInverse_of_surjective g.range_rangeRestrict
  obtain ⟨T,hT⟩ := (LinearMap.range g).subtype.exists_leftInverse_of_injective
    (LinearMap.range g).ker_subtype
  have hSval (z : LinearMap.range g) : g (S z)=z.val := by
    exact congrArg Subtype.val (LinearMap.congr_fun hS z)
  let P : Y →ₗ[K] LinearMap.ker g :=
    (LinearMap.id - S.comp g.rangeRestrict).codRestrict (LinearMap.ker g) (by
      intro y
      change g (y-S (g.rangeRestrict y))=0
      rw [map_sub,hSval]
      exact sub_self _)
  refine ⟨B,S,P,T,?_,hS,?_,?_,?_,hT⟩
  · ext y
    exact congrArg Subtype.val (LinearMap.congr_fun hB y)
  · ext y
    change y-S (g.rangeRestrict y)+S (g.rangeRestrict y)=y
    exact sub_add_cancel _ _
  · ext y
    change y.val-S (g.rangeRestrict y.val)=y.val
    have hz : g.rangeRestrict y.val=0 := Subtype.ext y.property
    rw [hz,map_zero,sub_zero]
  · ext z
    change S z-S (g.rangeRestrict (S z))=0
    have hsz := LinearMap.congr_fun hS z
    change g.rangeRestrict (S z)=z at hsz
    rw [hsz,sub_self]

variable {m n l : Type*} [Fintype m] [Fintype n] [Fintype l] [DecidableEq m]

/-- Compatible square blocks for an exact pair of literal matrices.  The
first block is the Jacobian on chosen parameter directions; the second
is the relation matrix on complementary equation coordinates. -/
theorem exists_matrix_split (J : Matrix m n K) (R : Matrix l m K)
    (hexact : LinearMap.range (Matrix.mulVecLin J)=LinearMap.ker (Matrix.mulVecLin R)) :
    ∃ (P : Matrix (Fin J.rank) m K)
      (Q : Matrix m (Fin J.rank) K)
      (V : Matrix m (Fin R.rank) K)
      (W : Matrix (Fin R.rank) m K)
      (T : Matrix (Fin R.rank) l K)
      (B : Matrix n (Fin J.rank) K),
      Q*P+V*W=1 ∧ P*J*B=1 ∧ T*R*V=1 ∧ R*Q=0 ∧ P*V=0 := by
  classical
  let f := Matrix.mulVecLin J
  let g := Matrix.mulVecLin R
  obtain ⟨B,S,P,T,hB,hS,hdecomp,hP,hPS,hT⟩ := exists_split f g hexact
  have hdim : Module.finrank K (LinearMap.ker g)=J.rank := by
    rw [←hexact]
    rfl
  let bU : Module.Basis (Fin J.rank) K (LinearMap.ker g) :=
    (Module.finBasis K (LinearMap.ker g)).reindex (finCongr hdim)
  let bV := Module.finBasis K (LinearMap.range g)
  let P0 := bU.equivFun.toLinearMap.comp P
  let Q0 := (LinearMap.ker g).subtype.comp bU.equivFun.symm.toLinearMap
  let V0 := S.comp bV.equivFun.symm.toLinearMap
  let W0 := bV.equivFun.toLinearMap.comp g.rangeRestrict
  let T0 := bV.equivFun.toLinearMap.comp T
  let B0 := B.comp bU.equivFun.symm.toLinearMap
  refine ⟨LinearMap.toMatrix' P0,LinearMap.toMatrix' Q0,LinearMap.toMatrix' V0,
    LinearMap.toMatrix' W0,LinearMap.toMatrix' T0,LinearMap.toMatrix' B0,?_,?_,?_,?_,?_⟩
  · apply Matrix.toLin'.injective
    simp only [map_add,Matrix.toLin'_mul,Matrix.toLin'_toMatrix',Matrix.toLin'_one]
    apply LinearMap.ext
    intro y
    change (bU.equivFun.symm (bU.equivFun (P y))).val+
      S (bV.equivFun.symm (bV.equivFun (g.rangeRestrict y)))=y
    simp only [LinearEquiv.symm_apply_apply]
    exact LinearMap.congr_fun hdecomp y
  · apply Matrix.toLin'.injective
    simp only [Matrix.toLin'_mul,Matrix.toLin'_toMatrix',Matrix.toLin'_one]
    apply LinearMap.ext
    intro x
    change bU.equivFun (P (f (B (bU.equivFun.symm x))))=x
    have hb := LinearMap.congr_fun hB (bU.equivFun.symm x)
    change f (B (bU.equivFun.symm x))=(bU.equivFun.symm x).val at hb
    have hp := LinearMap.congr_fun hP (bU.equivFun.symm x)
    change P (bU.equivFun.symm x).val=bU.equivFun.symm x at hp
    rw [hb,hp,LinearEquiv.apply_symm_apply]
  · apply Matrix.toLin'.injective
    simp only [Matrix.toLin'_mul,Matrix.toLin'_toMatrix',Matrix.toLin'_one]
    apply LinearMap.ext
    intro x
    change bV.equivFun (T (g (S (bV.equivFun.symm x))))=x
    have hSv := congrArg Subtype.val (LinearMap.congr_fun hS (bV.equivFun.symm x))
    change g (S (bV.equivFun.symm x))=(bV.equivFun.symm x).val at hSv
    have ht := LinearMap.congr_fun hT (bV.equivFun.symm x)
    change T (bV.equivFun.symm x).val=bV.equivFun.symm x at ht
    rw [hSv,ht,LinearEquiv.apply_symm_apply]
  · apply Matrix.toLin'.injective
    simp only [Matrix.toLin'_mul,Matrix.toLin'_toMatrix',map_zero]
    apply LinearMap.ext
    intro x
    exact (bU.equivFun.symm x).property
  · apply Matrix.toLin'.injective
    simp only [Matrix.toLin'_mul,Matrix.toLin'_toMatrix',map_zero]
    apply LinearMap.ext
    intro x
    change bU.equivFun (P (S (bV.equivFun.symm x)))=0
    have hps := LinearMap.congr_fun hPS (bV.equivFun.symm x)
    change P (S (bV.equivFun.symm x))=0 at hps
    rw [hps,map_zero]

end CycleQ2LinearExactSequenceSplit

#print axioms CycleQ2LinearExactSequenceSplit.exists_split
#print axioms CycleQ2LinearExactSequenceSplit.exists_matrix_split
end
end

/- Component: continuation_3/LinearKernelProjection.lean -/
section
/-! # A projection from a kernel with a compensating family

If every value of a linear map can be produced using directions killed by a
parameter projection, every parameter direction lifts to its kernel. This is
pure linear algebra; it makes no assertion about nonlinear integration.
-/

noncomputable section

namespace CycleQ2LinearKernelProjection

variable {K U V W T : Type*} [Ring K]
  [AddCommGroup U] [Module K U]
  [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]
  [AddCommGroup T] [Module K T]

theorem exists_kernel_correction
    (f : V →ₗ[K] W) (i : U →ₗ[K] V) (p : V →ₗ[K] T)
    (hip : p.comp i=0)
    (hrange : LinearMap.range f≤LinearMap.range (f.comp i)) (v : V) :
    ∃u : U, f (v-i u)=0 ∧ p (v-i u)=p v := by
  obtain ⟨u,hu⟩ := hrange (LinearMap.mem_range_self f v)
  refine ⟨u,?_,?_⟩
  · change f (i u)=f v at hu
    rw [map_sub,hu,sub_self]
  · have hpu : p (i u)=0 := congrArg (fun q : U →ₗ[K] T => q u) hip
    rw [map_sub,hpu,sub_zero]

theorem kernel_projection_surjective
    (f : V →ₗ[K] W) (i : U →ₗ[K] V) (p : V →ₗ[K] T)
    (hip : p.comp i=0)
    (hrange : LinearMap.range f≤LinearMap.range (f.comp i))
    (hp : Function.Surjective p) :
    Function.Surjective (p.comp (LinearMap.ker f).subtype) := by
  intro t
  obtain ⟨v,hv⟩ := hp t
  obtain ⟨u,hu,hup⟩ := exists_kernel_correction f i p hip hrange v
  exact ⟨⟨v-i u,hu⟩,hup.trans hv⟩

end CycleQ2LinearKernelProjection

#print axioms CycleQ2LinearKernelProjection.kernel_projection_surjective
end
end

/- Component: continuation_3/LinearKernelTrace.lean -/
section
/-! A strict rank increase after adjoining a scalar row is equivalent to a
kernel direction with nonzero scalar value. Over a field that direction can
be normalized to any prescribed value. Both directions use finite-dimensional
linear algebra and require no chosen matrix minor or explicit kernel vector.
-/

noncomputable section
set_option maxHeartbeats 300000

namespace CycleQ2LinearKernelTrace

variable {K V W U : Type*} [Field K]
  [AddCommGroup V] [Module K V] [Module.Finite K V]
  [AddCommGroup W] [Module K W] [AddCommGroup U] [Module K U]

theorem rank_le_of_kernel_le (f : V →ₗ[K] W) (g : V →ₗ[K] U)
    (hker : LinearMap.ker f≤LinearMap.ker g) :
    Module.finrank K (LinearMap.range g)≤Module.finrank K (LinearMap.range f) := by
  have hk := Submodule.finrank_mono hker
  have hf := f.finrank_range_add_finrank_ker
  have hg := g.finrank_range_add_finrank_ker
  omega

theorem exists_kernel_trace_one_of_rank_lt (f : V →ₗ[K] W) (ℓ : V →ₗ[K] K)
    (hrank : Module.finrank K (LinearMap.range f)<
      Module.finrank K (LinearMap.range (f.prod ℓ))) :
    ∃ v : V, f v=0 ∧ ℓ v=1 := by
  classical
  have hex : ∃ v : V, f v=0 ∧ ℓ v≠0 := by
    by_contra hn
    push_neg at hn
    have hk : LinearMap.ker f≤LinearMap.ker (f.prod ℓ) := by
      intro v hv
      change f v=0 at hv
      change (f v,ℓ v)=(0,0)
      exact Prod.ext hv (hn v hv)
    exact not_lt_of_ge (rank_le_of_kernel_le f (f.prod ℓ) hk) hrank
  obtain ⟨v,hv,hℓ⟩ := hex
  refine ⟨(ℓ v)⁻¹ • v,?_,?_⟩
  · simp only [map_smul,hv,smul_zero]
  · simp only [map_smul,smul_eq_mul,inv_mul_cancel₀ hℓ]

theorem rank_add_one_le_of_kernel_trace_one (f : V →ₗ[K] W) (ℓ : V →ₗ[K] K)
    (hex : ∃ v : V, f v=0 ∧ ℓ v=1) :
    Module.finrank K (LinearMap.range f)+1≤
      Module.finrank K (LinearMap.range (f.prod ℓ)) := by
  obtain ⟨v,hv,hℓ⟩ := hex
  have hle : LinearMap.ker (f.prod ℓ)≤LinearMap.ker f := by
    intro w hw
    change (f.prod ℓ) w=0 at hw
    change f w=0
    exact congrArg Prod.fst hw
  have hn : ¬LinearMap.ker f≤LinearMap.ker (f.prod ℓ) := by
    intro hk
    have hz := hk (show v∈LinearMap.ker f from hv)
    change (f.prod ℓ) v=0 at hz
    have hzero : ℓ v=0 := congrArg Prod.snd hz
    exact one_ne_zero (hℓ.symm.trans hzero)
  have hd := Submodule.finrank_lt_finrank_of_lt (lt_of_le_not_ge hle hn)
  have hf := f.finrank_range_add_finrank_ker
  have hg := (f.prod ℓ).finrank_range_add_finrank_ker
  omega

theorem exists_kernel_trace_value_of_rank_lt (f : V →ₗ[K] W) (ℓ : V →ₗ[K] K)
    (hrank : Module.finrank K (LinearMap.range f)<
      Module.finrank K (LinearMap.range (f.prod ℓ))) (a : K) :
    ∃ v : V, f v=0 ∧ ℓ v=a := by
  obtain ⟨v,hv,hℓ⟩ := exists_kernel_trace_one_of_rank_lt f ℓ hrank
  refine ⟨a • v,?_,?_⟩
  · simp only [map_smul,hv,smul_zero]
  · simp only [map_smul,hℓ,smul_eq_mul,mul_one]

end CycleQ2LinearKernelTrace

#print axioms CycleQ2LinearKernelTrace.exists_kernel_trace_one_of_rank_lt
#print axioms CycleQ2LinearKernelTrace.rank_add_one_le_of_kernel_trace_one
end
end

/- Component: continuation_3/cylinder_bridge/LinearRangeDescent.lean -/
section
/-! # Linear descent to the actual range

A linear map that kills the kernel of another map descends to that map's
actual range. The generic construction keeps the quotient universal
property separate from the concrete localized coefficient rings.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2LinearRangeDescent

variable {R M N P : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P]

def descendRange (f : M →ₗ[R] N) (g : M →ₗ[R] P)
    (h : LinearMap.ker f ≤ LinearMap.ker g) : LinearMap.range f →ₗ[R] P :=
  ((LinearMap.ker f).liftQ g h).comp f.quotKerEquivRange.symm.toLinearMap

theorem descendRange_apply_image (f : M →ₗ[R] N) (g : M →ₗ[R] P)
    (h : LinearMap.ker f ≤ LinearMap.ker g) (x : M) :
    descendRange f g h ⟨f x,⟨x,rfl⟩⟩=g x := by
  unfold descendRange
  rw [LinearMap.comp_apply,LinearEquiv.coe_coe,
    LinearMap.quotKerEquivRange_symm_apply_image]
  rfl

def kernelQuotientInjection (g : M →ₗ[R] P) (K : Submodule R M)
    (h : LinearMap.ker g=K) : (M ⧸ K) →ₗ[R] P :=
  K.liftQ g (le_of_eq h.symm)

theorem kernelQuotientInjection_injective (g : M →ₗ[R] P) (K : Submodule R M)
    (h : LinearMap.ker g=K) : Function.Injective (kernelQuotientInjection g K h) := by
  apply LinearMap.ker_eq_bot.mp
  exact Submodule.ker_liftQ_eq_bot' K g h.symm

end CycleQ2LinearRangeDescent

#print axioms CycleQ2LinearRangeDescent.descendRange_apply_image
#print axioms CycleQ2LinearRangeDescent.kernelQuotientInjection_injective
end
end

/- Component: continuation_3/cylinder_bridge/MatrixImageLocalization.lean -/
section
/-! Localization of the actual matrix image is the image of its localized
matrix.  This is proved using the span of the literal columns and mathlib's
localization of submodules, so local image trivializations apply to the
global image module itself. -/

noncomputable section
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2MatrixImageLocalization
open Matrix LinearMap

variable {R S α β : Type*} [CommRing R] [CommRing S]
  [Algebra R S] [Fintype α] [Fintype β]
  (p : Submonoid R) [IsLocalization p S]

def vectorMap : (α → R) →ₗ[R] (α → S) :=
  LinearMap.pi (fun i => (Algebra.linearMap R S).comp (LinearMap.proj i))

instance vectorMap_localized : IsLocalizedModule p (vectorMap (R := R) (S := S) (α := α)) :=
  IsLocalizedModule.pi p (fun _ : α => Algebra.linearMap R S)

theorem localized_image (M : Matrix α β R) :
    (LinearMap.range M.mulVecLin).localized' S p (vectorMap (R := R) (S := S))=
      LinearMap.range (M.map (algebraMap R S)).mulVecLin := by
  rw [Matrix.range_mulVecLin,Submodule.localized'_span,Matrix.range_mulVecLin]
  congr 1
  rw [←Set.range_comp]
  rfl

end CycleQ2MatrixImageLocalization

#print axioms CycleQ2MatrixImageLocalization.localized_image
end
end

/- Component: continuation_3/MatrixTraceAugment.lean -/
section
/-! Appending one actual scalar functional to a matrix preserves the
linear-map product description and commutes with coefficient maps. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2MatrixTraceAugment
open Matrix

variable {R S K : Type*} [CommRing R] [CommRing S] [Field K]
  {m n : Type*} [Fintype n]

def rowLinear (r : n → R) : (n → R) →ₗ[R] R :=
  dotProductBilin R R r

def augment (A : Matrix m n R) (r : n → R) : Matrix (m ⊕ Unit) n R :=
  fun i j => Sum.elim (fun k => A k j) (fun _ => r j) i

theorem augment_apply_left (A : Matrix m n R) (r x : n → R) (i : m) :
    (augment A r *ᵥ x) (Sum.inl i)=(A*ᵥx) i := rfl

theorem augment_apply_right (A : Matrix m n R) (r x : n → R) :
    (augment A r *ᵥ x) (Sum.inr ())=rowLinear r x := rfl

theorem augment_map (φ : R →+* S) (A : Matrix m n R) (r : n → R) :
    (augment A r).map φ=augment (A.map φ) (φ ∘ r) := by
  funext i j
  rcases i with i | i <;> rfl

theorem augment_ker (A : Matrix m n K) (r : n → K) :
    LinearMap.ker (Matrix.mulVecLin (augment A r))=
      LinearMap.ker ((Matrix.mulVecLin A).prod (rowLinear r)) := by
  ext x
  change (augment A r *ᵥ x=0) ↔ (A*ᵥx,rowLinear r x)=0
  constructor
  · intro h
    apply Prod.ext
    · funext i
      exact congrFun h (Sum.inl i)
    · exact congrFun h (Sum.inr ())
  · intro h
    funext i
    rcases i with i | i
    · exact congrFun (congrArg Prod.fst h) i
    · cases i
      exact congrArg Prod.snd h

theorem augment_rank [Fintype m] (A : Matrix m n K) (r : n → K) :
    (augment A r).rank=
      Module.finrank K (LinearMap.range ((Matrix.mulVecLin A).prod (rowLinear r))) := by
  classical
  have hA := (Matrix.mulVecLin (augment A r)).finrank_range_add_finrank_ker
  have hB := ((Matrix.mulVecLin A).prod (rowLinear r)).finrank_range_add_finrank_ker
  rw [augment_ker] at hA
  change (augment A r).rank+_= _ at hA
  omega

end CycleQ2MatrixTraceAugment

#print axioms CycleQ2MatrixTraceAugment.augment_rank
end
end

/- Component: continuation_3/cylinder_bridge/CechLinearAlgebra.lean -/
section
/-! Generic linear maps for the three-term Čech differential and surjective descent. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2CechLinearAlgebra

variable {R A B C T : Type*} [CommRing R]
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C] [AddCommGroup T] [Module R T]

def signedThree (f : A →ₗ[R] T) (g : B →ₗ[R] T) (h : C →ₗ[R] T) :
    A × B × C →ₗ[R] T where
  toFun x := f x.1-g x.2.1+h x.2.2
  map_add' x y := by
    change f (x.1+y.1)-g (x.2.1+y.2.1)+h (x.2.2+y.2.2)=_
    rw [map_add,map_add,map_add]
    abel
  map_smul' c x := by
    change f (c • x.1)-g (c • x.2.1)+h (c • x.2.2)=
      c • (f x.1-g x.2.1+h x.2.2)
    rw [map_smul,map_smul,map_smul,smul_add,smul_sub]

def descendSurjective (f : A →ₗ[R] B) (g : A →ₗ[R] T)
    (h : LinearMap.ker f≤LinearMap.ker g) (hf : Function.Surjective f) : B →ₗ[R] T :=
  (CycleQ2LinearRangeDescent.descendRange f g h).comp
    ((LinearMap.id : B →ₗ[R] B).codRestrict (LinearMap.range f) hf)

theorem descendSurjective_apply (f : A →ₗ[R] B) (g : A →ₗ[R] T)
    (h : LinearMap.ker f≤LinearMap.ker g) (hf : Function.Surjective f) (x : A) :
    descendSurjective f g h hf (f x)=g x :=
  CycleQ2LinearRangeDescent.descendRange_apply_image f g h x

end CycleQ2CechLinearAlgebra
end
end

/- Component: continuation_3/cylinder_bridge/LinearQuotientSurjectivity.lean -/
section
/-! Surjectivity and evaluation for the actual kernel quotient map. -/

noncomputable section
namespace CycleQ2LinearRangeDescent

variable {R M P : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P]

theorem kernelQuotientInjection_apply_mk (g : M →ₗ[R] P) (K : Submodule R M)
    (h : LinearMap.ker g=K) (x : M) :
    kernelQuotientInjection g K h (K.mkQ x)=g x := rfl

theorem kernelQuotientInjection_surjective (g : M →ₗ[R] P) (K : Submodule R M)
    (h : LinearMap.ker g=K) (hg : Function.Surjective g) :
    Function.Surjective (kernelQuotientInjection g K h) := by
  intro p
  obtain ⟨x,hx⟩ := hg p
  exact ⟨K.mkQ x,hx⟩

end CycleQ2LinearRangeDescent

#print axioms CycleQ2LinearRangeDescent.kernelQuotientInjection_surjective
end
end

/- Component: continuation_3/cylinder_bridge/CechLiftRelation.lean -/
section
/-! # Linear descent for a two-stage Čech lifting relation

The simultaneous lifts form a linear submodule. Surjectivity of its first
projection and the actual boundary criterion induce an injection between
the two cohomology quotients, independently of any chosen lifts.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2CechLiftRelation

variable {R P F C X G : Type*} [CommRing R]
  [AddCommGroup P] [Module R P] [AddCommGroup F] [Module R F]
  [AddCommGroup C] [Module R C] [AddCommGroup X] [Module R X]
  [AddCommGroup G] [Module R G]

variable (u : P →ₗ[R] X) (v : F →ₗ[R] X) (d : F →ₗ[R] G) (g : C →ₗ[R] G)

def lifts : Submodule R (P × F × C) where
  carrier L := v L.2.1=u L.1 ∧ d L.2.1=g L.2.2
  zero_mem' := by
    change v 0=u 0 ∧ d 0=g 0
    simp only [map_zero,and_self]
  add_mem' {L M} hL hM := by
    constructor
    · change v (L.2.1+M.2.1)=u (L.1+M.1)
      rw [map_add,map_add,hL.1,hM.1]
    · change d (L.2.1+M.2.1)=g (L.2.2+M.2.2)
      rw [map_add,map_add,hL.2,hM.2]
  smul_mem' a L hL := by
    constructor
    · change v (a • L.2.1)=u (a • L.1)
      rw [map_smul,map_smul,hL.1]
    · change d (a • L.2.1)=g (a • L.2.2)
      rw [map_smul,map_smul,hL.2]

def firstProjection : lifts u v d g →ₗ[R] P :=
  (LinearMap.fst R P (F×C)).comp (lifts u v d g).subtype

def lastProjection : lifts u v d g →ₗ[R] C :=
  (LinearMap.snd R F C).comp
    ((LinearMap.snd R P (F×C)).comp (lifts u v d g).subtype)

variable (K : Submodule R P) (H : Submodule R C)

def topClass : lifts u v d g →ₗ[R] C ⧸ H :=
  H.mkQ.comp (lastProjection u v d g)

variable (hex : ∀ p : P, ∃ f c, v f=u p ∧ d f=g c)
  (hzero : ∀ p f c, v f=u p → d f=g c → (c∈H ↔ p∈K))

include hex in
theorem firstProjection_surjective : Function.Surjective (firstProjection u v d g) := by
  intro p
  obtain ⟨f,c,hf,hc⟩ := hex p
  exact ⟨⟨(p,f,c),hf,hc⟩,rfl⟩

include hzero in
theorem ker_firstProjection_le :
    LinearMap.ker (firstProjection u v d g) ≤ LinearMap.ker (topClass u v d g H) := by
  intro L hL
  change H.mkQ L.val.2.2=0
  change (Submodule.Quotient.mk L.val.2.2 : C ⧸ H)=0
  rw [Submodule.Quotient.mk_eq_zero]
  apply (hzero L.val.1 L.val.2.1 L.val.2.2 L.property.1 L.property.2).mpr
  have hz : L.val.1=0 := hL
  rw [hz]
  exact K.zero_mem

def connecting : P →ₗ[R] C ⧸ H :=
  CycleQ2CechLinearAlgebra.descendSurjective
    (firstProjection u v d g) (topClass u v d g H)
    (ker_firstProjection_le u v d g K H hzero)
    (firstProjection_surjective u v d g hex)

theorem connecting_apply (p : P) (f : F) (c : C)
    (hf : v f=u p) (hc : d f=g c) :
    connecting u v d g K H hex hzero p=H.mkQ c := by
  exact CycleQ2CechLinearAlgebra.descendSurjective_apply
    (firstProjection u v d g) (topClass u v d g H)
    (ker_firstProjection_le u v d g K H hzero)
    (firstProjection_surjective u v d g hex) ⟨(p,f,c),hf,hc⟩

theorem ker_connecting : LinearMap.ker (connecting u v d g K H hex hzero)=K := by
  ext p
  change connecting u v d g K H hex hzero p=0 ↔ p∈K
  obtain ⟨f,c,hf,hc⟩ := hex p
  rw [connecting_apply u v d g K H hex hzero p f c hf hc]
  change (Submodule.Quotient.mk c : C ⧸ H)=0 ↔ p∈K
  rw [Submodule.Quotient.mk_eq_zero]
  exact hzero p f c hf hc

def quotientInjection : (P ⧸ K) →ₗ[R] (C ⧸ H) :=
  CycleQ2LinearRangeDescent.kernelQuotientInjection
    (connecting u v d g K H hex hzero) K (ker_connecting u v d g K H hex hzero)

theorem quotientInjection_injective :
    Function.Injective (quotientInjection u v d g K H hex hzero) :=
  CycleQ2LinearRangeDescent.kernelQuotientInjection_injective
    (connecting u v d g K H hex hzero) K (ker_connecting u v d g K H hex hzero)

end CycleQ2CechLiftRelation

#print axioms CycleQ2CechLiftRelation.quotientInjection_injective
end
end
