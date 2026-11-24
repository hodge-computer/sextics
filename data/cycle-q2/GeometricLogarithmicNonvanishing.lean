import Proposal.GeometricLocalDeRhamPurity

/-! The top normal Čech coefficient of the double logarithmic form is nonzero modulo
normal derivatives. In adapted coordinates this detects the actual two-form modulo both
single-open restrictions and exterior derivatives on their intersection.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false

noncomputable section

namespace CycleQ2LogDetection
section Weyl
variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- A normal derivative belonging to the socle is zero modulo an invariant
subspace, because multiplication by the normal parameter is locally nilpotent. -/
private theorem socle_derivative_mod (X D : Module.End ℚ V) (S : Submodule ℚ V)
    (h : ∀ m, D (X m) = m + X (D m))
    (hX : ∀ m ∈ S, X m ∈ S) (hD : ∀ m ∈ S, D m ∈ S)
    (m : V) (hm : X (D m) ∈ S) {n : ℕ} (hn : (X ^ n) m ∈ S) : m ∈ S := by
  have hDm (k : ℕ) : (X ^ (k+1)) (D m) ∈ S := by
    induction k with
    | zero => simpa using hm
    | succ k ih => rw [pow_succ', Module.End.mul_apply]; exact hX _ ih
  induction n with
  | zero => simpa using hn
  | succ n ih =>
    have hs := S.sub_mem (hD _ hn) (hDm n)
    rw [CycleQ2SupportedWeyl.power_rule X D h m n, add_sub_cancel_right] at hs
    exact ih ((S.smul_mem_iff (by positivity : ((n+1 : ℕ) : ℚ) ≠ 0)).mp hs)

/-- The joint socle injects into the top normal de Rham group. -/
theorem socle_detection (X Y Dx Dy : Module.End ℚ V)
    (hxx : ∀ m, Dx (X m) = m + X (Dx m))
    (hyy : ∀ m, Dy (Y m) = m + Y (Dy m))
    (hyx : ∀ m, Y (Dx m) = Dx (Y m)) (hdd : ∀ m, Dy (Dx m) = Dx (Dy m))
    (hnx : ∀ m, ∃ n : ℕ, (X^n) m = 0) (hny : ∀ m, ∃ n : ℕ, (Y^n) m = 0)
    (z : V) (hx : X z = 0) (hy : Y z = 0)
    (hb : z ∈ LinearMap.range Dx ⊔ LinearMap.range Dy) : z = 0 := by
  obtain ⟨_,⟨a,rfl⟩,_,⟨b,rfl⟩,h⟩ := Submodule.mem_sup.mp hb
  let S := LinearMap.range Dx
  have sy : ∀ m ∈ S, Y m ∈ S := by rintro _ ⟨u,rfl⟩; exact ⟨Y u,(hyx u).symm⟩
  have sd : ∀ m ∈ S, Dy m ∈ S := by rintro _ ⟨u,rfl⟩; exact ⟨Dy u,(hdd u).symm⟩
  have hb' : Y (Dy b) ∈ S := by
    have hi := congrArg Y h
    rw [map_add,hy,add_eq_zero_iff_eq_neg'] at hi
    rw [hi]
    exact S.neg_mem (sy _ ⟨a,rfl⟩)
  obtain ⟨n,hn⟩ := hny b
  have hbs := socle_derivative_mod Y Dy S hyy sy sd b hb' (n := n) (hn ▸ S.zero_mem)
  obtain ⟨u,hu⟩ : z ∈ S := h ▸ S.add_mem ⟨a,rfl⟩ (sd _ hbs)
  obtain ⟨n,hn⟩ := hnx u
  have hz : X (Dx u) ∈ (⊥ : Submodule ℚ V) := by simp [hu,hx]
  have hu' := socle_derivative_mod X Dx ⊥ hxx (by simp) (by simp) u hz (n := n) (hn ▸ (⊥ : Submodule ℚ V).zero_mem)
  simpa [show u = 0 from hu'] using hu.symm

end Weyl

section Fractions
open CycleQ2CechDenominatorTorsion
variable {R A B T : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing T]
  [Algebra R A] [Algebra R B] [Algebra R T]
  (x y : R) [IsLocalization.Away x A] [IsLocalization.Away y B] [IsLocalization.Away (x*y) T]

private theorem impossible_fraction_relation (hx : IsLeftRegular x)
    (sat : ∀ n m : ℕ, ∀ a : R, x ^ n ∣ y ^ m * a → x ^ n ∣ a)
    (I : Ideal R) (hI : I ≠ ⊤) (xi : x ∈ I) (yi : y ∈ I)
    (n m : ℕ) (a b : R) (h : x^n*y^m = y^(m+1)*a + x^(n+1)*b) : False := by
  have hdiv : x^n ∣ y^(m+1)*a := ⟨y^m-x*b, by linear_combination -h⟩
  obtain ⟨c,hc⟩ := sat n (m+1) a hdiv
  rw [hc] at h
  have h' : y^m*(1-y*c) = x*b := by
    apply (hx.pow n)
    change x^n*(y^m*(1-y*c)) = x^n*(x*b)
    linear_combination h
  obtain ⟨d,hd⟩ : x^1 ∣ 1-y*c := sat 1 m _ (by simpa only [pow_one] using (show x ∣ _ from ⟨b,h'⟩))
  rw [pow_one] at hd
  have h1 : (1:R) = x*d + y*c := by linear_combination hd
  exact hI ((Ideal.eq_top_iff_one _).mpr (h1 ▸ I.add_mem (I.mul_mem_right _ xi) (I.mul_mem_right _ yi)))

/-- The coefficient of the logarithmic form survives the Čech quotient at every
proper regular pair. -/
theorem inv_product_ne_zero (hx : IsLeftRegular x) (hy : IsLeftRegular y)
    (sat : ∀ n m : ℕ, ∀ a : R, x ^ n ∣ y ^ m * a → x ^ n ∣ a)
    (I : Ideal R) (hI : I ≠ ⊤) (xi : x ∈ I) (yi : y ∈ I) :
    (Submodule.Quotient.mk (IsLocalization.Away.invSelf (S := T) (x*y)) :
      T ⧸ boundaries A B T x y) ≠ 0 := by
  intro hz
  obtain ⟨_,⟨u,rfl⟩,_,⟨v,rfl⟩,h⟩ := Submodule.mem_sup.mp ((Submodule.Quotient.mk_eq_zero _).mp hz)
  obtain ⟨n,a,ha⟩ := IsLocalization.Away.surj x u
  obtain ⟨m,b,hb⟩ := IsLocalization.Away.surj y v
  let i := algebraMap R T
  let u' := fromFirst (T := T) x y u
  let v' := fromSecond (T := T) x y v
  have ua : u' * (i x)^n = i a := by
    simpa [u',i] using congrArg (fromFirst (T := T) x y) ha
  have vb : v' * (i y)^m = i b := by
    simpa [v',i] using congrArg (fromSecond (T := T) x y) hb
  have huv : (i x * i y) * (u' + v') = 1 := by
    have eq := IsLocalization.Away.mul_invSelf (S := T) (x*y)
    rw [map_mul,← h] at eq
    exact eq
  apply impossible_fraction_relation x y hx sat I hI xi yi n m (x*a) (y*b)
  apply CycleQ2RegularPairCech.first_injective (A := T) (hx.mul hy)
  change i _ = i _
  simp only [map_mul,map_pow,map_add,← ua,← vb,pow_succ]
  linear_combination -(i x)^n*(i y)^m*huv

private theorem first_annihilates :
    x • (Submodule.Quotient.mk (IsLocalization.Away.invSelf (S := T) (x*y)) :
      T ⧸ boundaries A B T x y) = 0 := by
  let b := IsLocalization.Away.invSelf (S := B) y
  apply (Submodule.Quotient.mk_eq_zero (boundaries A B T x y)).mpr
  apply le_sup_right (a := LinearMap.range (fromFirst (A := A) (T := T) x y).toLinearMap)
  refine ⟨b,?_⟩
  have uy : IsUnit (algebraMap R T y) := by
    simpa using ((IsLocalization.Away.algebraMap_isUnit (S := B) y).map (fromSecond (T := T) x y))
  apply uy.mul_left_cancel
  have hi := congrArg (fromSecond (T := T) x y) (IsLocalization.Away.mul_invSelf (S := B) y)
  simp only [map_mul,AlgHom.commutes,map_one] at hi
  change algebraMap R T y * fromSecond x y b = _
  rw [hi]
  dsimp only
  rw [Algebra.smul_def,mul_left_comm,← mul_assoc,← map_mul]
  exact (IsLocalization.Away.mul_invSelf (S := T) (x*y)).symm

private theorem second_annihilates :
    y • (Submodule.Quotient.mk (IsLocalization.Away.invSelf (S := T) (x*y)) :
      T ⧸ boundaries A B T x y) = 0 := by
  let a := IsLocalization.Away.invSelf (S := A) x
  apply (Submodule.Quotient.mk_eq_zero (boundaries A B T x y)).mpr
  apply le_sup_left (b := LinearMap.range (fromSecond (B := B) (T := T) x y).toLinearMap)
  refine ⟨a,?_⟩
  have ux : IsUnit (algebraMap R T x) := by
    simpa using ((IsLocalization.Away.algebraMap_isUnit (S := A) x).map (fromFirst (T := T) x y))
  apply ux.mul_left_cancel
  have hi := congrArg (fromFirst (T := T) x y) (IsLocalization.Away.mul_invSelf (S := A) x)
  simp only [map_mul,AlgHom.commutes,map_one] at hi
  change algebraMap R T x * fromFirst x y a = _
  rw [hi]
  dsimp only
  rw [Algebra.smul_def,← mul_assoc,← map_mul]
  exact (IsLocalization.Away.mul_invSelf (S := T) (x*y)).symm

end Fractions

section Chart
open CycleQ2CechDenominatorTorsion CycleQ2NormalCechDerivation
variable {R A B T : Type} [CommRing R] [CommRing A] [CommRing B] [CommRing T]
    [Algebra ℂ R] [Algebra ℂ A] [Algebra ℂ B] [Algebra ℂ T]
    [Algebra R A] [Algebra R B] [Algebra R T]
    [IsScalarTower ℂ R A] [IsScalarTower ℂ R B] [IsScalarTower ℂ R T]
    (x y : R) [IsLocalization.Away x A] [IsLocalization.Away y B]
    [IsLocalization.Away (x*y) T]

/-- The logarithmic coefficient at a regular pair in an affine chart is not a normal
curl modulo the two single opens. -/
theorem log_coefficient_not_curl (hx : IsLeftRegular x) (hy : IsLeftRegular y)
    (sat : ∀ n m : ℕ, ∀ a : R, x ^ n ∣ y ^ m * a → x ^ n ∣ a)
    (I : Ideal R) (hI : I ≠ ⊤) (xi : x ∈ I) (yi : y ∈ I)
    (dx dy : Derivation ℂ R R) (hxx : dx x = 1) (hyy : dy y = 1)
    (hxy : dx y = 0) (hdd : ∀ a, dy (dx a) = dx (dy a)) :
    (Submodule.Quotient.mk (IsLocalization.Away.invSelf (S := T) (x*y)) :
      T ⧸ boundaries A B T x y) ∉
      LinearMap.range (onParts x y dx) ⊔ LinearMap.range (onParts x y dy) := by
  let Q := T ⧸ boundaries A B T x y
  let : Module ℚ Q := Module.compHom Q (algebraMap ℚ ℂ)
  let : IsScalarTower ℚ ℂ Q := IsScalarTower.of_compHom ℚ ℂ Q
  let D (d : Derivation ℂ R R) : Module.End ℚ Q := (onParts x y d).restrictScalars ℚ
  let M (r : R) : Module.End ℚ Q := (Algebra.lsmul ℂ ℂ Q r).restrictScalars ℚ
  have spow (r : R) (v : Q) (n : ℕ) : (M r ^ n) v = r^n • v := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', Module.End.mul_apply,ih,pow_succ' r]
      exact (mul_smul r (r^n) v).symm
  have nx (v : Q) : ∃ n : ℕ, (M x ^ n) v = 0 := by
    obtain ⟨n,h,_⟩ := powers_kill x y v; exact ⟨n,(spow x v n).trans h⟩
  have ny (v : Q) : ∃ n : ℕ, (M y ^ n) v = 0 := by
    obtain ⟨n,_,h⟩ := powers_kill x y v; exact ⟨n,(spow y v n).trans h⟩
  have dmx (v : Q) : D dx (M x v) = v + M x (D dx v) := by
    change onParts x y dx (x • v) = v + x • onParts x y dx v
    rw [onParts_smul,hxx,one_smul,add_comm]
  have dmy (v : Q) : D dy (M y v) = v + M y (D dy v) := by
    change onParts x y dy (y • v) = v + y • onParts x y dy v
    rw [onParts_smul,hyy,one_smul,add_comm]
  have cross (v : Q) : M y (D dx v) = D dx (M y v) := by
    change y • onParts x y dx v = onParts x y dx (y • v)
    rw [onParts_smul,hxy,zero_smul,add_zero]
  intro hb
  apply inv_product_ne_zero x y hx hy sat I hI xi yi (A := A) (B := B) (T := T)
  apply socle_detection (M x) (M y) (D dx) (D dy) dmx dmy cross
    (fun v => onParts_commute x y dy dx hdd v) nx ny _
    (first_annihilates x y) (second_annihilates x y)
  obtain ⟨_,⟨u,rfl⟩,_,⟨v,rfl⟩,h⟩ := Submodule.mem_sup.mp hb
  exact Submodule.mem_sup.mpr ⟨_,⟨u,rfl⟩,_,⟨v,rfl⟩,h⟩

end Chart
end CycleQ2LogDetection

namespace CycleQ2LogDetection
open Module KaehlerDifferential CycleQ2FrameCurl CycleQ2CechDenominatorTorsion
open CycleQ2WeightedCoordinateExterior CycleQ2ExactFrameThreeDeRham
open CycleQ2NormalCechKahler CycleQ2ArbitraryFrameDifferential
open CycleQ2NormalCechFormBoundary CycleQ2NormalCechDerivation
open CycleQ2ExactFrameFirstDifferential CycleQ2GeometricLocalizedDerivations
open CycleQ2DoubleLogarithmicClass CycleQ2PrincipalGysinFunctions
variable {k R U V T : Type} [Field k] [CharZero k] [Algebra ℂ k]
    [CommRing R] [CommRing U] [CommRing V] [CommRing T]
    [Algebra k R] [Algebra k T] [Algebra k U] [Algebra k V]
    [Algebra R U] [Algebra R V] [Algebra R T]
    [IsScalarTower k R U] [IsScalarTower k R V] [IsScalarTower k R T]
    {n : ℕ} (b : Basis (Fin n) R Ω[R⁄k]) (u : Fin n → R) (hu : ∀ i, b i = D k R (u i))

include hu in
/-- The actual logarithmic overlap two-form on an adapted chart is not an
exterior derivative modulo restrictions of ordinary two-forms from the singly
localized charts. -/
theorem twoLog_not_boundary [IsNoetherianRing R] (a c : Fin n) (hac : a ≠ c)
    [IsLocalization.Away (u a) U] [IsLocalization.Away (u c) V]
    [IsLocalization.Away (u a * u c) T]
    (I : Ideal R) (hI : I ≠ ⊤) (ha : u a ∈ I) (hc : u c ∈ I)
    (f g : Tˣ) (hf : (f : T) = algebraMap R T (u a)) (hg : (g : T) = algebraMap R T (u c))
    (B : Basis (Fin n) T Ω[T⁄k]) (v : Fin n → T) (hB : ∀ i, B i = D k T (v i))
    (w : Form k T 1) :
    ¬ IsBoundary ((fromFirst (A := U) (T := T) (u a) (u c)).restrictScalars k)
      ((fromSecond (B := V) (T := T) (u a) (u c)).restrictScalars k) 2
      (twoLog (K := k) f g - d B 1 w) := by
  let _ : Algebra ℂ R := ((algebraMap k R).comp (algebraMap ℂ k)).toAlgebra
  let _ : Algebra ℂ U := ((algebraMap k U).comp (algebraMap ℂ k)).toAlgebra
  let _ : Algebra ℂ V := ((algebraMap k V).comp (algebraMap ℂ k)).toAlgebra
  let _ : Algebra ℂ T := ((algebraMap k T).comp (algebraMap ℂ k)).toAlgebra
  let _ : IsScalarTower ℂ k R := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower ℂ k T := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower ℂ R U := IsScalarTower.of_algebraMap_eq fun x => IsScalarTower.algebraMap_apply k R U (algebraMap ℂ k x)
  let _ : IsScalarTower ℂ R V := IsScalarTower.of_algebraMap_eq fun x => IsScalarTower.algebraMap_apply k R V (algebraMap ℂ k x)
  let _ : IsScalarTower ℂ R T := IsScalarTower.of_algebraMap_eq fun x => IsScalarTower.algebraMap_apply k R T (algebraMap ℂ k x)
  let M := Submonoid.powers (u a*u c)
  let r := fromFirst (A := U) (T := T) (u a) (u c)
  let s := fromSecond (B := V) (T := T) (u a) (u c)
  let bU := localFrame (T := U) b (Submonoid.powers (u a))
  let bV := localFrame (T := V) b (Submonoid.powers (u c))
  let Z := localFrame (T := T) b M
  let δ (i : Fin n) := (spatialDerivative b i).restrictScalars ℂ
  have hZ (i : Fin n) : Z i = D k T (algebraMap R T (u i)) := CycleQ2NormalCechFormBoundary.frame_exact b u hu M i
  have hr (i : Fin n) : onePullback (r.restrictScalars k) (bU i) = Z i := by
    rw [CycleQ2NormalCechFormBoundary.frame_exact b u hu _ i, onePullback_d,hZ]; exact congrArg (D k T) (r.commutes (u i))
  have hs (i : Fin n) : onePullback (s.restrictScalars k) (bV i) = Z i := by
    rw [CycleQ2NormalCechFormBoundary.frame_exact b u hu _ i, onePullback_d,hZ]; exact congrArg (D k T) (s.commutes (u i))
  have hδ (i : Fin n) (z : T) : localizedDerivation M T (δ i) z = spatialDerivative Z i z :=
    DFunLike.congr_fun (CycleQ2NormalCechKahler.direction_extends b M i).symm z
  have xx : δ a (u a) = 1 := by change spatialDerivative b a _ = 1; simp [partial_coordinate b u hu]
  have yy : δ c (u c) = 1 := by change spatialDerivative b c _ = 1; simp [partial_coordinate b u hu]
  have xy : δ a (u c) = 0 := by change spatialDerivative b a _ = 0; simp [partial_coordinate b u hu,hac.symm]
  obtain ⟨hx,hyx⟩ := CycleQ2NormalExteriorCech.exact_frame_regular b u hu a c hac
  obtain ⟨hy,_⟩ := CycleQ2NormalExteriorCech.exact_frame_regular b u hu c a hac.symm
  let S := boundaries U V T (u a) (u c)
  let z := IsLocalization.Away.invSelf (S := T) (u a*u c)
  have hdet := log_coefficient_not_curl (A := U) (B := V) (T := T) (u a) (u c) hx hy
    (CycleQ2RegularPairDivisibility.pow_dvd_of_dvd_pow_mul hx (CycleQ2RegularPairDivisibility.dvd_of_regular_mod hyx))
    I hI ha hc (δ a) (δ c) xx yy xy (partials_commute b u hu c a)
  have hlog : pair Z a c (twoLog (K := k) f g) = z := by
    rw [twoLog,pair_wedge]
    have hLf : logarithm (K := k) f = (↑f⁻¹ : T) • Z a := by rw [hZ,hf.symm]; rfl
    have hLg : logarithm (K := k) g = (↑g⁻¹ : T) • Z c := by rw [hZ,hg.symm]; rfl
    rw [hLf,hLg]
    simp only [map_smul, smul_eq_mul,Basis.coord_apply,Basis.repr_self_apply,
      if_neg hac,if_neg hac.symm,mul_zero,sub_zero]
    apply (IsLocalization.Away.algebraMap_isUnit (S := T) (u a*u c)).mul_left_cancel
    unfold z
    rw [IsLocalization.Away.mul_invSelf,map_mul,← hf,← hg]
    simp only [if_true,mul_one]
    rw [mul_mul_mul_comm (f:T) (g:T) (↑f⁻¹:T) (↑g⁻¹:T)]
    simp
  intro H
  obtain ⟨α,β,h⟩ := H
  obtain ⟨ω,rfl⟩ := (exteriorPower.oneEquiv T Ω[T⁄k]).symm.surjective w
  rw [CycleQ2AffineZeroOneForms.change_frame B v hB Z _ hZ,first_eq] at h
  change twoLog (K := k) f g - onOne Z ω = exteriorPullback (r.restrictScalars k) 2 α - exteriorPullback (s.restrictScalars k) 2 β at h
  have he := congrArg (pair Z a c) h
  simp only [map_sub,hlog,pair_onOne,pair_pull bU Z _ hr,pair_pull bV Z _ hs] at he
  have he' : z - (spatialDerivative Z a (Z.coord c ω) - spatialDerivative Z c (Z.coord a ω)) ∈ S := by
    rw [he]
    exact S.sub_mem (le_sup_left (b := LinearMap.range s.toLinearMap) ⟨_,rfl⟩)
      (le_sup_right (a := LinearMap.range r.toLinearMap) ⟨_,rfl⟩)
  apply hdet
  let q := S.mkQ
  have heq := (Submodule.Quotient.eq S).mpr he'
  change q z = q (_ - _) at heq
  rw [map_sub,← hδ,← hδ] at heq
  change q z ∈ _
  rw [heq]
  apply Submodule.sub_mem
  · exact le_sup_left (b := LinearMap.range (onParts (U := U) (V := V) (T := T) (u a) (u c) (δ c))) ⟨q _,rfl⟩
  · exact le_sup_right (a := LinearMap.range (onParts (U := U) (V := V) (T := T) (u a) (u c) (δ a))) ⟨q _,rfl⟩

end CycleQ2LogDetection

namespace CycleQ2LogDetection
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Module KaehlerDifferential
open CycleQ2FramedCechFormRow
open CycleQ2IntrinsicFramedAffineSite (FramedOpen frame frame_apply functions)
open CycleQ2SmoothRelativeFrames (sectionCoefficients)
open CycleQ2RelativeAffineOverlap (restrict)
open CycleQ2FramedAffineSite (restrict_comp)
open CycleQ2CechDenominatorTorsion (fromFirst fromSecond)
open CycleQ2ExactFrameThreeDeRham (exteriorPullback)
open CycleQ2WeightedCoordinateExterior (Form)
open CycleQ2IntrinsicDeRhamSheaves (relativeDeRhamInt)
open CycleQ2LocalPrincipalGysin (supportedQuotient)
open CycleQ2InjectiveCech (AbSheaf)

variable {k : Type} [Field k] [CharZero k] [Algebra ℂ k] {X : Scheme.{0}}
variable (p : X ⟶ Spec (CommRingCat.of k))
    (W : FramedOpen p 4)
    (u : Fin 4 → Γ(X,W.1))
    (hu : letI := (sectionCoefficients p W.1).toAlgebra;
      ∃ b : Basis (Fin 4) Γ(X,W.1) Ω[Γ(X,W.1)⁄k], ∀ i, b i = D k Γ(X,W.1) (u i))
local instance : HasDerivedCategory.{1} (AbSheaf (show TopCat from X)) := HasDerivedCategory.standard _
include hu

/-- At every point of the common zero locus of the two normal coordinates,
the actual logarithmic form is nonzero modulo the exterior differential
and both single-open restrictions. -/
theorem native_log_nonboundary [IsNoetherianRing Γ(X,W.1)] [SmoothOfRelativeDimension 4 p]
    (x : X) (hx : x ∈ W.1) (hz : x ∈ X.zeroLocus {u 0,u 1})
    (ω : ordinary p 4 (intersection p 4 W (u 0) (u 1)) 1) :
    let Z := intersection p 4 W (u 0) (u 1)
    let f := CycleQ2PrincipalLogSupportClass.restrictionUnit (u 0)
      (show Z.1 ≤ X.basicOpen (u 0) from inf_le_left)
    let g := CycleQ2PrincipalLogSupportClass.restrictionUnit (u 1)
      (show Z.1 ≤ X.basicOpen (u 1) from inf_le_right)
    ¬ IsBoundary p 4 W (u 0) (u 1) 2
      (CycleQ2IntrinsicLogSupportClass.logForm p 4 Z f g - deriv p 4 Z 1 ω) := by
  let f := u 0
  let g := u 1
  let A := Γ(X,W.1)
  let U := Γ(X,(singleOpen p 4 W f).1)
  let V := Γ(X,(singleOpen p 4 W g).1)
  let T := Γ(X,(intersection p 4 W f g).1)
  let hU : (singleOpen p 4 W f).1 ≤ W.1 := X.basicOpen_le f
  let hV : (singleOpen p 4 W g).1 ≤ W.1 := X.basicOpen_le g
  let hT : (intersection p 4 W f g).1 ≤ W.1 := (first p 4 W f g).le.trans hU
  let : Algebra k A := (sectionCoefficients p W.1).toAlgebra
  let : Algebra k U := (sectionCoefficients p (singleOpen p 4 W f).1).toAlgebra
  let : Algebra k V := (sectionCoefficients p (singleOpen p 4 W g).1).toAlgebra
  let : Algebra k T := (sectionCoefficients p (intersection p 4 W f g).1).toAlgebra
  let : Algebra A U := (restrict p hU).toRingHom.toAlgebra
  let : Algebra A V := (restrict p hV).toRingHom.toAlgebra
  let : Algebra A T := (restrict p hT).toRingHom.toAlgebra
  let : IsScalarTower k A U := IsScalarTower.of_algHom (restrict p hU)
  let : IsScalarTower k A V := IsScalarTower.of_algHom (restrict p hV)
  let : IsScalarTower k A T := IsScalarTower.of_algHom (restrict p hT)
  let : IsLocalization.Away f U := W.2.1.isLocalization_of_eq_basicOpen f (homOfLE hU) rfl
  let : IsLocalization.Away g V := W.2.1.isLocalization_of_eq_basicOpen g (homOfLE hV) rfl
  let : IsLocalization.Away (f*g) T :=
    W.2.1.isLocalization_of_eq_basicOpen (f*g) (homOfLE hT) (X.basicOpen_mul f g).symm
  let a : (intersection p 4 W f g).1 ≤ (singleOpen p 4 W f).1 := (first p 4 W f g).le
  let c : (intersection p 4 W f g).1 ≤ (singleOpen p 4 W g).1 := (second p 4 W f g).le
  have h₁ : restrict p a = (fromFirst (A := U) (T := T) f g).restrictScalars k :=
    eq_on_localization f _ _ (fun t => (AlgHom.congr_fun (restrict_comp p hU a) t).symm)
  have h₂ : restrict p c = (fromSecond (B := V) (T := T) f g).restrictScalars k :=
    eq_on_localization g _ _ (fun t => (AlgHom.congr_fun (restrict_comp p hV c) t).symm)
  obtain ⟨b,hb⟩ := hu
  let Z := intersection p 4 W f g
  let ρ := (fromFirst (A := U) (T := T) f g).restrictScalars k
  let σ := (fromSecond (B := V) (T := T) f g).restrictScalars k
  have bound (q : ℕ) (s : Form k T q) :
      IsBoundary p 4 W f g q s ↔ CycleQ2NormalCechFormBoundary.IsBoundary ρ σ q s := by
    change (∃ α : Form k U q, ∃ β : Form k V q, exteriorPullback (restrict p a) q α - exteriorPullback (restrict p c) q β = s) ↔ _
    rw [h₁,h₂]
    exact exists_congr (fun _ => exists_congr fun _ => eq_comm)

  let I : Ideal A := (IsLocalRing.maximalIdeal _).comap (X.presheaf.germ W.1 x hx).hom
  have hI : I ≠ ⊤ := Ideal.IsPrime.ne_top inferInstance
  have hmem (e : A) (he : e ∈ ({f,g} : Set A)) : e ∈ I := by
    change ¬ IsUnit (X.presheaf.germ W.1 x hx e)
    intro hun
    exact (X.mem_zeroLocus_iff _ _).mp hz e he ((X.mem_basicOpen e x hx).mpr hun)
  exact fun h => twoLog_not_boundary (U := U) (V := V) b u hb 0 1 (by decide) I hI
    (hmem f (by simp)) (hmem g (by simp)) _ _ (CycleQ2PrincipalLogSupportClass.restrictionUnit_val f _)
    (CycleQ2PrincipalLogSupportClass.restrictionUnit_val g _) (frame p 4 Z) (functions p 4 Z)
    (frame_apply p 4 Z) ω ((bound 2 _).mp h)

end CycleQ2LogDetection

namespace CycleQ2LogDetection
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open CycleQ2InjectiveCech (AbSheaf Sections freeOpen freeOpenMap freeOpenSections)
open CycleQ2FramedCechFormRow
open CycleQ2IntrinsicFramedAffineSite (FramedOpen)
open CycleQ2IntrinsicDeRhamSheaves
open CycleQ2LocalPrincipalGysin (cover)
open CycleQ2DerivedDoubleSupport (sectionMap)
open CycleQ2PrincipalLogSupportClass (restrictionUnit)
open CycleQ2IntrinsicLogSupportClass (logForm shiftedSection)
open CycleQ2SupportedCechExt (overlapBoundary)

private theorem overlap_sections {Y : TopCat.{0}} (S : (Opens.grothendieckTopology Y).MayerVietorisSquare)
    (T : AbSheaf Y) (m : S.shortComplex.X₂ ⟶ T) :
    freeOpenSections T S.X₁ (S.shortComplex.f ≫ m) ∈ (overlapBoundary S T).range := by
  let z := (freeOpenSections T S.X₂ (biprod.inl ≫ m),freeOpenSections T S.X₃ (biprod.inr ≫ m))
  refine ⟨z,?_⟩
  have hm : m = biprod.desc (biprod.inl ≫ m) (biprod.inr ≫ m) := by
    apply biprod.hom_ext' <;> simp
  conv_rhs => rw [hm]
  change _ = freeOpenSections T S.X₁
    (biprod.lift (freeOpenMap S.f₁₂.le) (-(freeOpenMap S.f₁₃.le)) ≫ _)
  erw [biprod.lift_desc,Preadditive.neg_comp,map_add,map_neg,
    CycleQ2InjectiveCech.freeOpenSections_naturality T S.f₁₂.le,
    CycleQ2InjectiveCech.freeOpenSections_naturality T S.f₁₃.le]
  simp [z,overlapBoundary,sub_eq_add_neg]
  rfl

variable {k : Type} [Field k] [CharZero k] [Algebra ℂ k] {X : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of k)) [SmoothOfRelativeDimension 4 p]
    (W : FramedOpen p 4) [IsNoetherianRing Γ(X,W.1)]
    (u : Fin 4 → Γ(X,W.1))
    (hu : letI := (CycleQ2SmoothRelativeFrames.sectionCoefficients p W.1).toAlgebra
      ∃ b : Module.Basis (Fin 4) Γ(X,W.1) (KaehlerDifferential k Γ(X,W.1)),
        ∀ i, b i = KaehlerDifferential.D k Γ(X,W.1) (u i))

private abbrev Z := intersection p 4 W (u 0) (u 1)
private abbrev S : (Opens.grothendieckTopology (show TopCat from X)).MayerVietorisSquare :=
  cover (u 0) (u 1)
private abbrev K : CochainComplex (AbSheaf (show TopCat from X)) ℤ := relativeDeRhamInt p 4
private abbrev z := logForm p 4 (Z p W u)
  (restrictionUnit (u 0) (show (Z p W u).1 ≤ _ from inf_le_left))
  (restrictionUnit (u 1) (show (Z p W u).1 ≤ _ from inf_le_right))

include hu
/-- On the actual affine adapted graph chart, the chain representative whose double
connecting class defines the local Gysin class admits no boundary decomposition. -/
theorem native_section_nondecomposable (x : X) (hx : x ∈ W.1) (hz : x ∈ X.zeroLocus {u 0,u 1}) :
    ¬ ∃ (a : (S p W u).shortComplex.X₁ ⟶ (K p).X 1)
        (b : (S p W u).shortComplex.X₂ ⟶ (K p).X 2),
      sectionMap (2:ℤ) (S p W u) (shiftedSection p 4 (Z p W u) (z p W u)) =
        ((S p W u).shortComplex.f ≫ b) + (a ≫ (K p).d 1 2) := by
  rintro ⟨a,b,hab⟩
  let T := (K p).X 2
  let O := (S p W u).X₁
  let c : Sections T O := shiftedSection p 4 (Z p W u) (z p W u)
  let l : freeOpen O ⟶ T := (S p W u).shortComplex.f ≫ b
  let r : freeOpen O ⟶ T := a ≫ (K p).d 1 2
  have he : c = freeOpenSections T O l + freeOpenSections T O r := calc
    _ = freeOpenSections T O ((freeOpenSections T O).symm c) :=
      ((freeOpenSections T O).apply_symm_apply c).symm
    _ = freeOpenSections T O (l+r) := congrArg (fun t : freeOpen O ⟶ T => freeOpenSections T O t) hab
    _ = _ := map_add (freeOpenSections T O) l r
  let v := freeOpenSections ((K p).X 1) O a
  have hd : freeOpenSections T O (a ≫ (K p).d 1 2) =
      ((K p).d 1 2).hom.app (op O) v := (CycleQ2CechTwoToDerived.freeOpenSections_postcomp O a _).symm
  have hrep : ∃ t : Sections ((K p).X 1) O,
      c - ((K p).d 1 2).hom.app (op O) t ∈ (overlapBoundary (S p W u) T).range := by
    refine ⟨v,?_⟩
    rw [he,show freeOpenSections T O r = _ from hd,add_sub_cancel_right]
    exact overlap_sections _ _ _
  obtain ⟨t,ht⟩ := (primitive_mod_boundary_iff p 4 W (u 0) (u 1) 1 c).mp hrep
  have hcoord : coordinates p 4 (Z p W u) 2 c = z p W u :=
    (coordinates p 4 (Z p W u) 2).apply_symm_apply _
  rw [hcoord] at ht
  exact native_log_nonboundary p W u hu x hx hz t ht

end CycleQ2LogDetection

#print axioms CycleQ2LogDetection.native_section_nondecomposable
