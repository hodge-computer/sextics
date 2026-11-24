import Proposal.GeometricSurfaceBindings
import Proposal.GeometricCartierCharacter

section SourceCartierCyclicAction

set_option autoImplicit false
set_option Elab.async false
noncomputable section

section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SeedCechRestrictions

open MvPolynomial CycleQ2SegreTangentLocal CycleQ2SeedQuotientFiniteFree
  CycleQ2SeedCechThreeOpen CycleQ2SeedCechLocalization CycleQ2SeedCechLocalizedBasis

variable (R : Type*) [CommRing R]

instance seedLocalAway (r ι : R) (s : Finset (Fin 3)) :
    IsLocalization.Away (algebraMap (Base R) (SeedRing r ι) (baseProduct R s))
      (SeedLocal R r ι s) := by
  have hh : Algebra.algebraMapSubmonoid (SeedRing r ι)
      (Submonoid.powers (baseProduct R s)) =
      Submonoid.powers (algebraMap (Base R) (SeedRing r ι) (baseProduct R s)) := by
    exact Submonoid.map_powers _ _
  rw [IsLocalization.Away, ← hh]
  infer_instance

theorem baseProduct_dvd {s t : Finset (Fin 3)} (hst : s ⊆ t) :
    baseProduct R s ∣ baseProduct R t :=
  Finset.prod_dvd_prod_of_subset s t (fun i ↦ X i) hst

theorem seedProduct_isUnit (r ι : R) {s t : Finset (Fin 3)} (hst : s ⊆ t) :
    IsUnit (algebraMap (SeedRing r ι) (SeedLocal R r ι t)
      (algebraMap (Base R) (SeedRing r ι) (baseProduct R s))) := by
  apply IsLocalization.Away.isUnit_of_dvd (S := SeedLocal R r ι t)
    (algebraMap (Base R) (SeedRing r ι) (baseProduct R t))
  exact map_dvd (algebraMap (Base R) (SeedRing r ι)) (baseProduct_dvd R hst)

end CycleQ2SeedCechRestrictions

end

section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 10000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SeedCyclicAction

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2SegreTangentLocal

variable {R : Type*} [CommRing R]

def actionValues (ζ : R) : Fin 5 → Poly R :=
  ![C (ζ^2)*X 0,C (ζ^2)*X 1,C ζ*X 2,X 3,X 4]

def polynomialAction (ζ : R) : Poly R →ₐ[R] Poly R := aeval (actionValues ζ)

@[simp] theorem polynomialAction_X (ζ : R) (i : Fin 5) :
    polynomialAction ζ (X i)=actionValues ζ i := aeval_X _ _

@[simp] theorem polynomialAction_C (ζ c : R) : polynomialAction ζ (C c)=C c := aeval_C _ _

def characterExponent (e : FullExponent) : ℕ := 2*e 0+2*e 1+e 2

theorem polynomialAction_monomial (ζ : R) (e : FullExponent) (c : R) :
    polynomialAction ζ (monomial e c)=C (ζ^characterExponent e)*monomial e c := by
  rw [polynomialAction,aeval_monomial,monomial_eq]
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [actionValues,characterExponent,Fin.prod_univ_succ,Fin.prod_univ_zero,
    Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.reduceSucc,Matrix.head_cons,Matrix.tail_cons,
    mul_one,MvPolynomial.algebraMap_eq,map_pow,map_mul,mul_pow,pow_add,pow_mul]
  ring

theorem pow_eq_mod_three (ζ : R) (hζ : ζ^3=1) (n : ℕ) : ζ^n=ζ^(n%3) := by
  calc
    ζ^n=ζ^(n%3+3*(n/3)) := congrArg (fun k : ℕ => ζ^k) (Nat.mod_add_div n 3).symm
    _=ζ^(n%3) := by rw [pow_add,pow_mul,hζ,one_pow,mul_one]

theorem polynomialAction_homogeneous (ζ : R) (hζ : ζ^3=1)
    (p : Poly R) (d : ℕ) (ch : ZMod 3) (hp : HG p (d,ch)) :
    polynomialAction ζ p=C (ζ^ch.val)*p := by
  classical
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  conv_rhs => rw [p.as_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  rw [polynomialAction_monomial]
  have hg := hp (mem_support_iff.mp he)
  rw [fullGrading_weight] at hg
  have hc : characterExponent e%3=ch.val := by
    simpa only [characterExponent,ZMod.val_natCast] using
      congrArg (fun g : ℕ × ZMod 3 => g.2.val) hg
  rw [pow_eq_mod_three ζ hζ,hc]

theorem polynomialAction_smoothH (ζ : R) (hζ : ζ^3=1) (ι : R) :
    polynomialAction ζ (smoothH ι)=smoothH ι := by
  simpa using polynomialAction_homogeneous ζ hζ (smoothH ι) 3 0 (smoothH_homogeneous ι)

theorem polynomialAction_smoothF (ζ : R) (hζ : ζ^3=1) (r ι : R) :
    polynomialAction ζ (smoothF r ι)=smoothF r ι := by
  simpa using polynomialAction_homogeneous ζ hζ (smoothF r ι) 6 0 (smoothF_homogeneous r ι)

def seedAction (ζ : R) (hζ : ζ^3=1) (r ι : R) : SeedRing r ι →ₐ[R] SeedRing r ι :=
  Ideal.quotientMapₐ (equationsIdeal (smoothH ι) (smoothF r ι)) (polynomialAction ζ) (by
    apply Ideal.span_le.mpr
    intro p hp
    rcases hp with rfl | ⟨rfl⟩
    · change polynomialAction ζ (smoothH ι) ∈ equationsIdeal (smoothH ι) (smoothF r ι)
      rw [polynomialAction_smoothH ζ hζ]
      exact Ideal.subset_span (by simp [equationsIdeal])
    · change polynomialAction ζ (smoothF r ι) ∈ equationsIdeal (smoothH ι) (smoothF r ι)
      rw [polynomialAction_smoothF ζ hζ]
      exact Ideal.subset_span (by simp [equationsIdeal]))

@[simp] theorem seedAction_mk (ζ : R) (hζ : ζ^3=1) (r ι : R) (p : Poly R) :
    seedAction ζ hζ r ι (Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) p)=
      Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) (polynomialAction ζ p) := rfl

end CycleQ2SeedCyclicAction

end

section
set_option maxHeartbeats 500000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SeedCyclicLocalization

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2SegreTangentLocal CycleQ2SeedQuotientFiniteFree CycleQ2SeedCechThreeOpen
  CycleQ2SeedCechLocalization CycleQ2SeedCechLocalizedBasis CycleQ2SeedCechRestrictions
  CycleQ2SeedCyclicAction

variable {R : Type*} [CommRing R]

def baseScalars (ζ : R) : Fin 3 → R := ![ζ^2,ζ,1]
def baseFactor (ζ : R) (s : Finset (Fin 3)) : R := ∏ i∈s, baseScalars ζ i
def baseProductPoly (s : Finset (Fin 3)) : Poly R := remainingInclusion R (baseProduct R s)

theorem cube_root_isUnit (ζ : R) (hζ : ζ^3=1) : IsUnit ζ := by
  apply IsUnit.of_mul_eq_one (ζ^2)
  calc
    ζ*ζ^2=ζ^3 := by ring
    _=1 := hζ

theorem baseFactor_isUnit (ζ : R) (hζ : ζ^3=1) (s : Finset (Fin 3)) : IsUnit (baseFactor ζ s) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [baseFactor]
  | @insert i s hi ih =>
    rw [baseFactor,Finset.prod_insert hi]
    apply IsUnit.mul _ ih
    fin_cases i
    · exact (cube_root_isUnit ζ hζ).pow 2
    · exact cube_root_isUnit ζ hζ
    · exact isUnit_one

theorem actionValues_remaining (ζ : R) (i : Fin 3) :
    actionValues ζ (remainingIndex i)=C (baseScalars ζ i)*X (remainingIndex i) := by
  fin_cases i <;> simp [actionValues,remainingIndex,baseScalars]

theorem polynomialAction_baseProduct (ζ : R) (s : Finset (Fin 3)) :
    polynomialAction ζ (baseProductPoly (R:=R) s)=C (baseFactor ζ s)*baseProductPoly s := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [baseProductPoly,baseProduct,baseFactor]
  | @insert i s hi ih =>
    have hp : baseProductPoly (R:=R) (insert i s)=X (remainingIndex i)*baseProductPoly s := by
      simp [baseProductPoly,baseProduct,hi,remainingInclusion]
    have hf : baseFactor ζ (insert i s)=baseScalars ζ i*baseFactor ζ s := by
      simp [baseFactor,hi]
    rw [hp,map_mul,polynomialAction_X,actionValues_remaining,ih,hf,map_mul]
    ring

theorem seedAction_baseProduct (ζ : R) (hζ : ζ^3=1) (r ι : R) (s : Finset (Fin 3)) :
    seedAction ζ hζ r ι (algebraMap (Base R) (SeedRing r ι) (baseProduct R s))=
      Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) (C (baseFactor ζ s))*
        algebraMap (Base R) (SeedRing r ι) (baseProduct R s) := by
  change seedAction ζ hζ r ι
    (Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) (baseProductPoly s))=_
  rw [seedAction_mk,polynomialAction_baseProduct,map_mul]
  rfl

theorem acted_baseProduct_isUnit (ζ : R) (hζ : ζ^3=1) (r ι : R) (s : Finset (Fin 3)) :
    IsUnit (algebraMap (SeedRing r ι) (SeedLocal R r ι s)
      (seedAction ζ hζ r ι (algebraMap (Base R) (SeedRing r ι) (baseProduct R s)))) := by
  rw [seedAction_baseProduct,map_mul]
  apply IsUnit.mul
  · exact (baseFactor_isUnit ζ hζ s).map
      (((algebraMap (SeedRing r ι) (SeedLocal R r ι s)).comp
        (Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)))).comp C)
  · exact seedProduct_isUnit R r ι (Finset.Subset.refl s)

def localAction (ζ : R) (hζ : ζ^3=1) (r ι : R) (s : Finset (Fin 3)) :
    SeedLocal R r ι s →+* SeedLocal R r ι s :=
  IsLocalization.Away.lift
    (S:=SeedLocal R r ι s) (P:=SeedLocal R r ι s)
    (g:=(algebraMap (SeedRing r ι) (SeedLocal R r ι s)).comp (seedAction ζ hζ r ι).toRingHom)
    (algebraMap (Base R) (SeedRing r ι) (baseProduct R s))
    (acted_baseProduct_isUnit ζ hζ r ι s)

@[simp] theorem localAction_algebraMap (ζ : R) (hζ : ζ^3=1) (r ι : R)
    (s : Finset (Fin 3)) (q : SeedRing r ι) :
    localAction ζ hζ r ι s (algebraMap (SeedRing r ι) (SeedLocal R r ι s) q)=
      algebraMap (SeedRing r ι) (SeedLocal R r ι s) (seedAction ζ hζ r ι q) :=
  IsLocalization.Away.lift_eq _ (acted_baseProduct_isUnit ζ hζ r ι s) q

@[simp] theorem localAction_mk (ζ : R) (hζ : ζ^3=1) (r ι : R)
    (s : Finset (Fin 3)) (p : Poly R) :
    localAction ζ hζ r ι s
      (algebraMap (SeedRing r ι) (SeedLocal R r ι s)
        (Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) p))=
      algebraMap (SeedRing r ι) (SeedLocal R r ι s)
        (Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) (polynomialAction ζ p)) := by
  rw [localAction_algebraMap,seedAction_mk]

end CycleQ2SeedCyclicLocalization

end

#print axioms CycleQ2SeedCyclicAction.polynomialAction_homogeneous
#print axioms CycleQ2SeedCyclicAction.seedAction
#print axioms CycleQ2SeedCyclicLocalization.localAction_mk

end
end SourceCartierCyclicAction

section SourceCartierProjectedAction

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace CycleQ2OrbitTraceBridge

section LinearOrbit

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- For a fixed ambient test of character `zeta`, the three responses use
the inverse characters: `v + zeta^2 g(v) + zeta g^2(v)`. -/
def twistedOrbit (ζ : R) (g : V →ₗ[R] V) (v : V) : V :=
  v + ζ ^ 2 • g v + ζ • g (g v)

/-- On the character-one eigenspace, the correctly twisted orbit is three
times the class. An untwisted orbit does not have this property. -/
theorem twistedOrbit_eq_three_smul (ζ : R) (hζ : ζ ^ 3 = 1)
    (g : V →ₗ[R] V) (v : V) (hv : g v = ζ • v) :
    twistedOrbit ζ g v = (3 : R) • v := by
  have hc : 1 + ζ ^ 2 * ζ + ζ * (ζ * ζ) = (3 : R) := by
    linear_combination 2 * hζ
  unfold twistedOrbit
  simp only [hv, map_smul]
  calc
    v + ζ ^ 2 • (ζ • v) + ζ • (ζ • (ζ • v)) =
        (1 + ζ ^ 2 * ζ + ζ * (ζ * ζ)) • v := by
      simp only [add_smul, smul_smul, one_smul]
    _ = (3 : R) • v := by rw [hc]

/-- The dual character is sufficient: the original class need not itself
already lie in the character-one eigenspace. -/
theorem pairing_twistedOrbit (ζ : R) (hζ : ζ ^ 3 = 1)
    (g : V →ₗ[R] V) (φ : V →ₗ[R] R)
    (hφ : ∀ v, φ (g v) = ζ * φ v) (v : V) :
    φ (twistedOrbit ζ g v) = 3 * φ v := by
  simp only [twistedOrbit, map_add, map_smul, hφ, smul_eq_mul]
  linear_combination (2 * φ v) * hζ

/-- The inverse-character factor is necessary: the ordinary orbit kills
a character-one vector for a primitive cube root. -/
theorem untwistedOrbit_eq_zero (ζ : R) (hζ : ζ ^ 2 + ζ + 1 = 0)
    (g : V →ₗ[R] V) (v : V) (hv : g v = ζ • v) :
    v + g v + g (g v) = 0 := by
  have hc : 1 + ζ + ζ * ζ = 0 := by
    linear_combination hζ
  simp only [hv, map_smul]
  calc
    v + ζ • v + ζ • (ζ • v) = (1 + ζ + ζ * ζ) • v := by
      simp only [add_smul, smul_smul, one_smul]
    _ = 0 := by rw [hc, zero_smul]

end LinearOrbit


section ActualLocalization

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2SegreTangentLocal CycleQ2SeedQuotientFiniteFree
  CycleQ2SeedCechThreeOpen CycleQ2SeedCechLocalization CycleQ2SeedCechLocalizedBasis
  CycleQ2SeedCyclicAction CycleQ2SeedCyclicLocalization

variable {R : Type*} [CommRing R]

/-- The actual localization action fixes the coefficient ring. -/
theorem localAction_scalar (ζ : R) (hζ : ζ ^ 3 = 1) (r ι : R)
    (s : Finset (Fin 3)) (c : R) :
    localAction ζ hζ r ι s (algebraMap R (SeedLocal R r ι s) c) =
      algebraMap R (SeedLocal R r ι s) c := by
  rw [IsScalarTower.algebraMap_apply R (SeedRing r ι) (SeedLocal R r ι s)]
  change localAction ζ hζ r ι s
      (algebraMap (SeedRing r ι) (SeedLocal R r ι s)
        (Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) (C c))) =
    algebraMap (SeedRing r ι) (SeedLocal R r ι s)
      (Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) (C c))
  rw [localAction_mk, polynomialAction_C]

/-- The existing ring action, with its proved coefficient linearity. -/
def localLinearAction (ζ : R) (hζ : ζ ^ 3 = 1) (r ι : R)
    (s : Finset (Fin 3)) : SeedLocal R r ι s →ₗ[R] SeedLocal R r ι s where
  __ := (localAction ζ hζ r ι s).toAddMonoidHom
  map_smul' c q := by
    simp only [RingHom.id_apply, Algebra.smul_def]
    change localAction ζ hζ r ι s (algebraMap R (SeedLocal R r ι s) c * q) =
      algebraMap R (SeedLocal R r ι s) c * localAction ζ hζ r ι s q
    rw [map_mul, localAction_scalar]

@[simp] theorem localLinearAction_apply (ζ : R) (hζ : ζ ^ 3 = 1) (r ι : R)
    (s : Finset (Fin 3)) (q : SeedLocal R r ι s) :
    localLinearAction ζ hζ r ι s q = localAction ζ hζ r ι s q := rfl

/-- The triple-open denominator is `x1*x2*x3`, of trivial character. -/
theorem baseFactor_univ (ζ : R) (hζ : ζ ^ 3 = 1) :
    baseFactor ζ (Finset.univ : Finset (Fin 3)) = 1 := by
  calc
    baseFactor ζ (Finset.univ : Finset (Fin 3)) = ζ ^ 2 * ζ := by
      simp [baseFactor, baseScalars, Fin.prod_univ_succ]
    _ = ζ ^ 3 := by ring
    _ = 1 := hζ


end ActualLocalization

end CycleQ2OrbitTraceBridge

namespace CycleQ2GeometricCoordinateCharacter

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2SegreTangentLocal CycleQ2SeedQuotientFiniteFree
  CycleQ2SeedCechThreeOpen CycleQ2SeedCechLocalization CycleQ2SeedCechLocalizedBasis
  CycleQ2SeedCechRestrictions CycleQ2SeedCyclicAction CycleQ2SeedCyclicLocalization
  CycleQ2GeometricSurfaceCoordinates CycleQ2GeometricSeedNormalIdeals
  CycleQ2OrbitTraceBridge

theorem characterExponent_cast (e : FullExponent) :
    (characterExponent e : ZMod 3) = Finsupp.weight characterWeight e := by
  rw [Finsupp.weight_eq_sum]
  simp [characterWeight,characterExponent,Fin.sum_univ_succ,Finsupp.sum_fintype,nsmul_eq_mul]
  <;> ring

/-- Eigenvalues of the literal diagonal polynomial substitution, with no
assumed action on a comparison module. -/
theorem polynomialAction_character {R : Type*} [CommRing R]
    (ζ : R) (hζ : ζ^3=1) (p : Poly R) (χ : ZMod 3)
    (hp : p.IsWeightedHomogeneous characterWeight χ) :
    polynomialAction ζ p = C (ζ^χ.val)*p := by
  classical
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  conv_rhs => rw [p.as_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  rw [polynomialAction_monomial]
  have hχ := (characterExponent_cast e).trans (hp (mem_support_iff.mp he))
  have hc : characterExponent e % 3 = χ.val := by
    simpa only [ZMod.val_natCast] using congrArg ZMod.val hχ
  rw [pow_eq_mod_three ζ hζ,hc]

/-- Clearing the original triple denominator proves the eigenvalue in the
original seed localization itself. -/
theorem localAction_character_fraction (ζ : ℂ) (hζ : ζ^3=1) (r : ℂ)
    (q : SeedLocal ℂ r Complex.I Finset.univ) (p : Poly ℂ) (n : ℕ) (χ : ZMod 3)
    (hp : p.IsWeightedHomogeneous characterWeight χ)
    (hfrac : q * algebraMap (SeedRing r Complex.I) (SeedLocal ℂ r Complex.I Finset.univ)
      (algebraMap (Base ℂ) (SeedRing r Complex.I) (baseProduct ℂ Finset.univ ^ n)) =
      algebraMap (SeedRing r Complex.I) (SeedLocal ℂ r Complex.I Finset.univ)
        (Ideal.Quotient.mk (equationsIdeal (smoothH Complex.I) (smoothF r Complex.I)) p)) :
    localAction ζ hζ r Complex.I Finset.univ q = ζ^χ.val • q := by
  let φ := algebraMap (SeedRing r Complex.I) (SeedLocal ℂ r Complex.I Finset.univ)
  let π := Ideal.Quotient.mk (equationsIdeal (smoothH Complex.I) (smoothF r Complex.I))
  let den := φ (algebraMap (Base ℂ) (SeedRing r Complex.I) (baseProduct ℂ Finset.univ ^ n))
  have hden : IsUnit den := by
    dsimp [den,φ]
    simpa only [map_pow] using
      (seedProduct_isUnit ℂ r Complex.I (Finset.Subset.refl Finset.univ)).pow n
  have hfixed : localAction ζ hζ r Complex.I Finset.univ den = den := by
    dsimp [den,φ]
    simp only [map_pow,localAction_algebraMap,seedAction_baseProduct,
      baseFactor_univ ζ hζ,map_one,one_mul]
  change q * den = φ (π p) at hfrac
  have he := congrArg (localAction ζ hζ r Complex.I Finset.univ) hfrac
  rw [map_mul,hfixed,localAction_mk,polynomialAction_character ζ hζ p χ hp,
    map_mul,map_mul] at he
  change localAction ζ hζ r Complex.I Finset.univ q * den =
    φ (π (C (ζ^χ.val))) * φ (π p) at he
  rw [← hfrac] at he
  obtain ⟨u,hu⟩ := hden
  have he' := congrArg (fun z : SeedLocal ℂ r Complex.I Finset.univ =>
    z * (↑(u⁻¹) : SeedLocal ℂ r Complex.I Finset.univ)) he
  rw [← hu] at he'
  have hcancel : localAction ζ hζ r Complex.I Finset.univ q =
      φ (π (C (ζ^χ.val))) * q := by
    simpa only [mul_assoc,u.mul_inv,mul_one] using he'
  rw [Algebra.smul_def,
    IsScalarTower.algebraMap_apply ℂ (SeedRing r Complex.I) (SeedLocal ℂ r Complex.I Finset.univ)]
  exact hcancel

/-- The same actual coordinate projection has its character under the
original localized diagonal action. -/
theorem projected_localAction (ζ : ℂ) (hζ : ζ^3=1) (r : ℂ)
    (q : CoordinateLocal r 1 Finset.univ) (χ : ZMod 3) :
    localAction ζ hζ r Complex.I Finset.univ
      (seedCoordinateEquiv r Finset.univ (coordinateProject r Finset.univ χ q)) =
    ζ^χ.val • seedCoordinateEquiv r Finset.univ (coordinateProject r Finset.univ χ q) := by
  obtain ⟨n,p,rfl⟩ := exists_polynomialFraction r q
  rw [coordinateProject_polynomialFraction]
  apply localAction_character_fraction ζ hζ r _ _ n χ
    (weightedHomogeneousComponent_isWeightedHomogeneous (w := characterWeight) χ p)
  have hh := congrArg (seedCoordinateEquiv r Finset.univ)
    (polynomialFraction_spec r n (weightedHomogeneousComponent characterWeight χ p))
  simp only [map_mul,seedCoordinateEquiv_base,map_pow,seedRingEquiv_coordinateProduct,
    seedRingEquiv_quotient] at hh
  simpa only [map_pow] using hh

/-- The correctly twisted orbit of the projected original section is
exactly three times that same section under the original action. -/
theorem projected_character_one_twistedOrbit (ζ : ℂ) (hζ : ζ^3=1) (r : ℂ)
    (q : CoordinateLocal r 1 Finset.univ) :
    twistedOrbit ζ (localLinearAction ζ hζ r Complex.I Finset.univ)
      (seedCoordinateEquiv r Finset.univ (coordinateProject r Finset.univ 1 q)) =
      (3 : ℂ) • seedCoordinateEquiv r Finset.univ (coordinateProject r Finset.univ 1 q) := by
  apply twistedOrbit_eq_three_smul ζ hζ
  have hχ : (1 : ZMod 3).val = 1 := by decide
  simpa only [localLinearAction_apply,hχ,pow_one] using
    projected_localAction ζ hζ r q 1

end CycleQ2GeometricCoordinateCharacter

#print axioms CycleQ2GeometricCoordinateCharacter.polynomialAction_character
#print axioms CycleQ2GeometricCoordinateCharacter.projected_localAction
#print axioms CycleQ2GeometricCoordinateCharacter.projected_character_one_twistedOrbit

end
end SourceCartierProjectedAction

section SourceCartierTwistedOrbit

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace CycleQ2GeometricCoordinateCharacter

open CycleQ2SeedCechThreeOpen CycleQ2GeometricSurfaceCoordinates
  CycleQ2GeometricLaurentTop CycleQ2GeometricHomogeneousWeight
  CycleQ2GeometricCartierCech CycleQ2GeometricFourOpenCech
  CycleQ2NormalConnecting CycleQ2OrbitTraceBridge

/-- The actual seed-localization orbit, transported through the fixed
identity-on-polynomials coordinate equivalence. -/
def coordinateTwistedOrbit (ζ : ℂ) (hζ : ζ^3=1) (r : ℂ)
    (q : CoordinateLocal r 1 Finset.univ) : CoordinateLocal r 1 Finset.univ :=
  (seedCoordinateEquiv r Finset.univ).symm
    (twistedOrbit ζ (localLinearAction ζ hζ r Complex.I Finset.univ)
      (seedCoordinateEquiv r Finset.univ q))

/-- The literal action on the same projected coordinate representative
gives three copies of that representative. -/
theorem coordinateTwistedOrbit_projected (ζ : ℂ) (hζ : ζ^3=1) (r : ℂ)
    (q : CoordinateLocal r 1 Finset.univ) :
    coordinateTwistedOrbit ζ hζ r (coordinateProject r Finset.univ 1 q) =
      (3 : ℕ) • coordinateProject r Finset.univ 1 q := by
  simp only [coordinateTwistedOrbit,projected_character_one_twistedOrbit,
    ofNat_smul_eq_nsmul,map_nsmul,RingEquiv.symm_apply_apply]

theorem coordinateTwistedOrbit_projected_coefficient (ζ : ℂ) (hζ : ζ^3=1)
    (r : ℂ) (q : CoordinateLocal r 1 Finset.univ) (ab : ShiftIndex)
    (e : LaurentExponent) :
    (coordinateLaurent r Finset.univ
      (coordinateTwistedOrbit ζ hζ r (coordinateProject r Finset.univ 1 q)) ab).coeff e =
      (3 : ℂ) * (coordinateLaurent r Finset.univ
        (coordinateProject r Finset.univ 1 q) ab).coeff e := by
  rw [coordinateTwistedOrbit_projected,map_nsmul]
  change ((3 : ℕ) • (coordinateLaurent r Finset.univ
    (coordinateProject r Finset.univ 1 q) ab)).coeff e =
      (3 : ℂ) * (coordinateLaurent r Finset.univ
        (coordinateProject r Finset.univ 1 q) ab).coeff e
  rw [AddMonoidAlgebra.coeff_smul,Finsupp.smul_apply]
  simp only [nsmul_eq_mul,Nat.cast_ofNat]

/-- The orbit stays in the actual character-one, weight-zero module. -/
theorem coordinateTwistedOrbit_projected_grade (ζ : ℂ) (hζ : ζ^3=1)
    (r : ℂ) (q : HomogeneousCoordinateTop r) (ab : ShiftIndex) :
    HasGrade ab (0,1) (coordinateLaurent r Finset.univ
      (coordinateTwistedOrbit ζ hζ r (coordinateProject r Finset.univ 1 q.val)) ab) := by
  intro e he
  rw [coordinateTwistedOrbit_projected_coefficient,
    projected_homogeneous_grade r 1 q ab e he,mul_zero]

/-- The same projected Cartier class has a nonzero negative coefficient
after the actual correctly twisted orbit. -/
theorem literal_projected_twistedOrbit_negative (ζ : ℂ) (hζ : ζ^3=1)
    (d : TwoCocycles (coordinateScalarSystem 57))
    (hcd : CartierCoordinateDescent 57 (cartierCycle 57 1 derivativeA 0) d)
    (q : HomogeneousCoordinateTop 57)
    (hq : q.val = coordinateTopRepresentative 57 d) :
    ∃ ab e, (∀ i, e i < 0) ∧
      (coordinateLaurent 57 Finset.univ
        (coordinateTwistedOrbit ζ hζ 57
          (coordinateProject 57 Finset.univ 1 q.val)) ab).coeff e ≠ 0 := by
  obtain ⟨ab,e,he,hc⟩ := literal_character_one_negative d hcd q hq
  refine ⟨ab,e,he,?_⟩
  rw [coordinateTwistedOrbit_projected_coefficient]
  exact mul_ne_zero (by norm_num) hc

/-- The orbit of this named representative cannot be the boundary of any
three actual pair-open sections, at any pole order. -/
theorem literal_projected_twistedOrbit_nonboundary (ζ : ℂ) (hζ : ζ^3=1)
    (d : TwoCocycles (coordinateScalarSystem 57))
    (hcd : CartierCoordinateDescent 57 (cartierCycle 57 1 derivativeA 0) d)
    (q : HomogeneousCoordinateTop 57)
    (hq : q.val = coordinateTopRepresentative 57 d) :
    ¬ ∃ (p01 : CoordinateLocal 57 1 {0,1}) (p02 : CoordinateLocal 57 1 {0,2})
      (p12 : CoordinateLocal 57 1 {1,2}),
      coordinateRestriction 57 1 (show ({1,2} : Finset (Fin 3)) ⊆ Finset.univ by simp) p12 -
        coordinateRestriction 57 1 (show ({0,2} : Finset (Fin 3)) ⊆ Finset.univ by simp) p02 +
        coordinateRestriction 57 1 (show ({0,1} : Finset (Fin 3)) ⊆ Finset.univ by simp) p01 =
      coordinateTwistedOrbit ζ hζ 57 (coordinateProject 57 Finset.univ 1 q.val) := by
  intro hb
  obtain ⟨ab,e,he,hc⟩ := literal_projected_twistedOrbit_negative ζ hζ d hcd q hq
  exact hc ((coordinate_all_negative_zero_iff 57 _).mpr hb ab e he)

end CycleQ2GeometricCoordinateCharacter

#print axioms CycleQ2GeometricCoordinateCharacter.coordinateTwistedOrbit_projected
#print axioms CycleQ2GeometricCoordinateCharacter.coordinateTwistedOrbit_projected_grade
#print axioms CycleQ2GeometricCoordinateCharacter.literal_projected_twistedOrbit_nonboundary

end
end SourceCartierTwistedOrbit
