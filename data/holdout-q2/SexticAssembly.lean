import Proposal.EndpointRegular
import Proposal.HoldoutActiveClearing
import Proposal.HoldoutDenominator

/-! Assembly of one endpoint certificate. The hypotheses concern only the
four-variable cubic solver and its matrix norm on the good coefficient fiber.
Homogeneous coefficient clearing, the six-variable derivative identities, and
complex denominator legality are proved here. -/

noncomputable section
namespace HoldoutSexticAssembly
open MvPolynomial HoldoutEndpointHorizontal

def activePolynomials (k : ℂ) : Fin 4 → HoldoutQ2.Clearing.BasePoly :=
  ![X 0^2,X 1^2,X 2^2+C (k^2)*X 5^2,C k*X 2*X 5]

theorem activePolynomials_homogeneous (k : ℂ) (j : Fin 4) :
    (activePolynomials k j).IsHomogeneous 2 := by
  fin_cases j
  · exact isHomogeneous_X_pow 0 2
  · exact isHomogeneous_X_pow 1 2
  · exact (isHomogeneous_X_pow 2 2).add ((isHomogeneous_X_pow 5 2).C_mul (k^2))
  · exact ((isHomogeneous_X ℂ 2).C_mul k).mul (isHomogeneous_X ℂ 5)

theorem activePolynomials_map (k : ℂ) (j : Fin 4) :
    HoldoutQ2.Clearing.baseMap (activePolynomials k j)=active k j := by
  fin_cases j <;> simp [activePolynomials,active,coordinate,constant]

theorem activeImage_eq (k : ℂ) :
    HoldoutQ2.Clearing.activeImage k (activePolynomials k)=activeMap (HoldoutQ2.Clearing.regularParameterMap k) k := by
  unfold HoldoutQ2.Clearing.activeImage activeMap
  congr 1
  funext j
  exact activePolynomials_map k j

def regularCubic (k : ℂ) : HoldoutQ2.Clearing.ActivePoly k :=
  MvPolynomial.map (algebraMap HoldoutQ2.Clearing.Parameters (HoldoutQ2.Clearing.Regular k)) (HoldoutEndpointTarget.cubic k)
def regularSource (k : ℂ) : HoldoutQ2.Clearing.ActivePoly k :=
  MvPolynomial.map (algebraMap HoldoutQ2.Clearing.Parameters (HoldoutQ2.Clearing.Regular k)) HoldoutEndpointTarget.source

theorem regular_pullback (k : ℂ) (P : MvPolynomial (Fin 4) HoldoutQ2.Clearing.Parameters) :
    activeMap (HoldoutQ2.Clearing.regularParameterMap k) k
      (MvPolynomial.map (algebraMap HoldoutQ2.Clearing.Parameters (HoldoutQ2.Clearing.Regular k)) P)=
      HoldoutEndpointTarget.pullback k P := by
  induction P using MvPolynomial.induction_on with
  | C r =>
      simp only [MvPolynomial.map_C,activeMap,eval₂Hom_C,
        HoldoutQ2.Clearing.regularParameterMap_algebraMap,HoldoutEndpointTarget.pullback_C]
      rw [HoldoutEndpointRegular.parameterMap_eq]
  | add p q hp hq => simp only [map_add,hp,hq]
  | mul_X p j hp =>
      simp only [map_mul,MvPolynomial.map_X,activeMap,eval₂Hom_X,
        HoldoutEndpointTarget.pullback_X] at hp ⊢
      rw [hp]
      simp

theorem regularCubic_pullback {k : ℂ} (hk : k^2+k+1=0) :
    activeMap (HoldoutQ2.Clearing.regularParameterMap k) k (regularCubic k)=baseMap HoldoutEndpointTarget.F := by
  rw [regularCubic,regular_pullback,HoldoutEndpointTarget.pullback_cubic hk]

theorem regularSource_density (k : ℂ) :
    2*baseMap (HoldoutEndpointLift.delta k)*
      activeMap (HoldoutQ2.Clearing.regularParameterMap k) k (regularSource k)=
      baseMap (HoldoutEndpointTarget.reflectionTarget k) := by
  rw [regularSource,regular_pullback,HoldoutEndpointTarget.pullback_source_density]

/-- The active denominator specialization expected from the cubic solver. -/
def activeNormFiber (k : ℂ) : HoldoutQ2.Clearing.ActivePoly k →+* Polynomial ℂ :=
  eval₂Hom (Polynomial.C.comp (RegularSpecialization.specialize (HoldoutQ2.Clearing.goodParameters k)))
    ![1,1,Polynomial.X^2,0]

theorem fiber_ratioBase (k : ℂ) (P : HoldoutQ2.Clearing.BasePoly) :
    HoldoutDenominator.fiber k (HoldoutQ2.Clearing.ratioBase k P)=HoldoutDenominator.fiber k P := by
  have h : (HoldoutDenominator.fiber k).comp (HoldoutQ2.Clearing.ratioBase k)=HoldoutDenominator.fiber k := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp [HoldoutQ2.Clearing.ratioBase]
    · intro i
      fin_cases i <;>
        simp [HoldoutQ2.Clearing.ratioBase,HoldoutQ2.Clearing.ratioValues,HoldoutDenominator.fiberValues]
  exact congrArg (fun f : HoldoutQ2.Clearing.BasePoly →+* Polynomial ℂ => f P) h

theorem fiber_xa (k : ℂ) : HoldoutDenominator.fiber k HoldoutQ2.Clearing.xa=1 := by
  simp [HoldoutQ2.Clearing.xa,HoldoutDenominator.fiberValues]

theorem fiber_clearing (k : ℂ) :
    HoldoutDenominator.fiber k (HoldoutEndpointLift.clearing (R := ℂ))=1 := by
  simp [HoldoutEndpointLift.clearing,HoldoutDenominator.fiberValues]

theorem fiber_activeFibre (k : ℂ) (P : HoldoutQ2.Clearing.ActivePoly k) :
    HoldoutDenominator.fiber k (HoldoutQ2.Clearing.activeFibre k (activePolynomials k) P)=activeNormFiber k P := by
  have h : (HoldoutDenominator.fiber k).comp (HoldoutQ2.Clearing.activeFibre k (activePolynomials k))=
      activeNormFiber k := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [HoldoutQ2.Clearing.activeFibre,activeNormFiber]
    · intro j
      simp only [RingHom.comp_apply,HoldoutQ2.Clearing.activeFibre,eval₂Hom_X,fiber_ratioBase,
        activeNormFiber]
      fin_cases j <;>
        simp [activePolynomials,fiber_ratioBase,HoldoutDenominator.fiberValues]
  exact congrArg (fun f : HoldoutQ2.Clearing.ActivePoly k →+* Polynomial ℂ => f P) h

/-- A cubic pole-two field with a legal matrix-norm specialization gives the
actual endpoint certificate on the unchanged sextic. -/
theorem hasCertificate_endpoint_from_cubic {k : ℂ} (hk : k^2+k+1=0)
    (D : HoldoutQ2.Clearing.ActivePoly k) (N : Fin 4 → HoldoutQ2.Clearing.ActivePoly k) (d : ℕ)
    (hD : D.IsHomogeneous d) (hN : ∀ i, (N i).IsHomogeneous (d+3))
    (hsrc : 2*(∑ i, N i*pderiv i (regularCubic k))=D*regularSource k)
    (hdiv : D*(∑ i, pderiv i (N i))=∑ i, N i*pderiv i D)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M K : Matrix ι ι ℂ) (s : ℂ) (hs : s≠0)
    (hK : (M^3+(5 : ℂ) • (1 : Matrix ι ι ℂ))*K=1)
    (hD_fiber : activeNormFiber k D=Polynomial.C s*HoldoutDenominator.normFiber M) :
    HodgeComputer.HasCertificate HoldoutEndpointTarget.F
      (HoldoutEndpointTarget.reflectionTarget k) 2 := by
  obtain ⟨n,q,u,Q,P,hu,hq,hQhom,hPhom,hQ,hP,hQfiber,hPfiber⟩ :=
    HoldoutQ2.Clearing.exists_q2_representatives_with_fibre D N d hD hN
      (activePolynomials k) (activePolynomials_homogeneous k)
  rw [activeImage_eq] at hQ
  simp only [activeImage_eq] at hP
  have hsource := HoldoutEndpointFractionLift.homogeneous_clearing_source
    (HoldoutQ2.Clearing.regularParameterMap k) k hk (HoldoutEndpointRegular.horizontal_regularParameterMap k)
    (regularCubic k) (regularSource k) D N HoldoutEndpointTarget.F
    (HoldoutEndpointTarget.reflectionTarget k) u Q P
    (regularCubic_pullback hk) (regularSource_density k) hQ hP hsrc
  have hdivergence := HoldoutEndpointFractionLift.homogeneous_clearing_divergence
    (HoldoutQ2.Clearing.regularParameterMap k) k hk (HoldoutEndpointRegular.horizontal_regularParameterMap k)
    D N u Q P hQ hP hdiv
  have hfiber : HoldoutDenominator.fiber k (HoldoutEndpointLift.denominator Q)=
      Polynomial.C (HoldoutQ2.Clearing.goodParameters k q*s)*HoldoutDenominator.normFiber M := by
    have hh := congrArg (HoldoutDenominator.fiber k) hQfiber
    rw [fiber_ratioBase] at hh
    simp only [map_mul,map_pow,HoldoutDenominator.fiber_C,fiber_xa,one_pow,mul_one,
      fiber_activeFibre,hD_fiber] at hh
    simpa only [HoldoutEndpointLift.denominator,map_mul,fiber_clearing,one_mul,
      map_mul,mul_assoc] using hh
  have hlegal := HoldoutDenominator.denominator_legal_of_scaled_normFiber hk
    (HoldoutEndpointLift.denominator Q) M K (HoldoutQ2.Clearing.goodParameters k q*s)
    (mul_ne_zero hq hs) hK hfiber
  have hne := HoldoutDenominator.denominator_ne_zero_of_legal _ hlegal
  refine ⟨2*(n+d)+4,HoldoutEndpointLift.denominator Q,
    HoldoutEndpointLift.numerators k (P 0) (P 1) (P 2) (P 3),0,?_,?_,?_,?_,?_⟩
  · exact hne
  · exact HoldoutEndpointLift.denominator_homogeneous hQhom
  · intro i
    have hh := HoldoutEndpointLift.numerators_homogeneous k
      (hPhom 0) (hPhom 1) (hPhom 2) (hPhom 3) i
    have hdeg : 2*(n+d+3)+5=(2*(n+d)+4)+6*2-5 := by omega
    rw [hdeg] at hh
    exact hh
  · exact hlegal
  · simpa only [HodgeComputer.defect,Nat.cast_ofNat,mul_zero] using
      HoldoutEndpointLift.lift_strict_q2 k HoldoutEndpointTarget.F
        (HoldoutEndpointTarget.reflectionTarget k) Q (P 0) (P 1) (P 2) (P 3)
        hsource hdivergence

end HoldoutSexticAssembly

#print axioms HoldoutSexticAssembly.hasCertificate_endpoint_from_cubic
