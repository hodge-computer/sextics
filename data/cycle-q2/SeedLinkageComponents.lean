import Proposal.CurveAndSeedCechCoordinates

/-!
# The seed linkage components and their graded factor ideals
-/

set_option Elab.async false

/- Component: continuation_3/SeedLinkageIdeals.lean -/
section
/-! The literal linkage ideals in the actual smooth seed quotient. -/

noncomputable section
set_option maxHeartbeats 1000000
set_option Elab.async false
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SeedLinkageIdeals

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2IncidenceJacobian CycleQ2IncidenceJacobianNaturality CycleQ2SegreTangentLocal
  CycleQ2CurveRestriction CycleQ2CurveRestrictionReflection

variable {R : Type*} [CommRing R]

def linkageGenerator (s : Side) (r : R) : Fin 5 → Poly R :=
  match s with
  | .left => CycleQ2SegreSeed.linkageE (X 0^2) (C r*X 1*X 3) (X 4) (X 2^2)
  | .right => CycleQ2SegreSeed.linkageEprime (X 0^2) (C r*X 1*X 3) (X 4) (X 2^2)

def generatorDegree : Fin 5 → ℕ := ![4,6,6,6,6]
def generatorCharacter : Fin 5 → ℕ := ![1,0,1,2,0]

private theorem regrade {p : Poly R} {a b : Grade} (hp : HG p a) (h : a=b) : HG p b := h ▸ hp

theorem linkageGenerator_homogeneous (s : Side) (r : R) (j : Fin 5) :
    HG (linkageGenerator s r j) (generatorDegree j,(generatorCharacter j:ZMod 3)) := by
  let a : Poly R := X 0^2
  let b : Poly R := C r*X 1*X 3
  let c : Poly R := X 4
  let d : Poly R := X 2^2
  have ha : HG a (2,1) := regrade ((isWeightedHomogeneous_X R fullGrading 0).pow 2) (by decide)
  have hb : HG b (2,2) := by
    apply regrade (p:=b) _ (show fullGrading 1+fullGrading 3=(2,2) from by decide)
    simpa only [b,mul_assoc] using
      ((isWeightedHomogeneous_X R fullGrading 1).mul (isWeightedHomogeneous_X R fullGrading 3)).C_mul r
  have hc : HG c (2,0) := isWeightedHomogeneous_X R fullGrading 4
  have hd : HG d (2,2) := regrade ((isWeightedHomogeneous_X R fullGrading 2).pow 2) (by decide)
  cases s <;> fin_cases j
  · change HG (a*c+b*d) (4,1)
    exact (regrade (ha.mul hc) (by decide)).add (regrade (hb.mul hd) (by decide))
  · change HG (a^3-b^3) (6,0)
    exact (regrade (ha.pow 3) (by decide)).sub (regrade (hb.pow 3) (by decide))
  · change HG (a^2*d+b^2*c) (6,1)
    exact (regrade ((ha.pow 2).mul hd) (by decide)).add (regrade ((hb.pow 2).mul hc) (by decide))
  · change HG (a*d^2-b*c^2) (6,2)
    exact (regrade (ha.mul (hd.pow 2)) (by decide)).sub (regrade (hb.mul (hc.pow 2)) (by decide))
  · change HG (c^3+d^3) (6,0)
    exact (regrade (hc.pow 3) (by decide)).add (regrade (hd.pow 3) (by decide))
  · change HG (a*c+b*d) (4,1)
    exact (regrade (ha.mul hc) (by decide)).add (regrade (hb.mul hd) (by decide))
  · change HG (a^3+d^3) (6,0)
    exact (regrade (ha.pow 3) (by decide)).add (regrade (hd.pow 3) (by decide))
  · change HG (a^2*b-c*d^2) (6,1)
    exact (regrade ((ha.pow 2).mul hb) (by decide)).sub (regrade (hc.mul (hd.pow 2)) (by decide))
  · change HG (a*b^2+c^2*d) (6,2)
    exact (regrade (ha.mul (hb.pow 2)) (by decide)).add (regrade ((hc.pow 2).mul hd) (by decide))
  · change HG (-b^3+c^3) (6,0)
    exact (regrade (hb.pow 3) (by decide)).neg.add (regrade (hc.pow 3) (by decide))

def curveGeneratorQuotient (s : Side) (r : R) : Fin 5 → CurvePoly R :=
  match s with
  | .left =>
      let a : CurvePoly R := X 0^2
      let b : CurvePoly R := C r*X 1*X 3
      let d : CurvePoly R := X 2^2
      ![-d,a^2+a*b+b^2,(a+b)*d,d^2,0]
  | .right =>
      let a : CurvePoly R := (X 0+X 2)^2
      let b : CurvePoly R := C (4*r)*X 1*X 3
      let d : CurvePoly R := (X 0-X 2)^2
      ![2*b,2*(a^2-a*d+d^2),2*b*(a-d),2*b^2,0]

theorem substitution_linkageGenerator (s : Side) (r : R) (j : Fin 5) :
    substitution s r (linkageGenerator s r j)=curveGeneratorQuotient s r j*quadric s r := by
  cases s <;> fin_cases j <;>
    simp [linkageGenerator,CycleQ2SegreSeed.linkageE,CycleQ2SegreSeed.linkageEprime,
      curveGeneratorQuotient,quadric,map_add,map_sub,map_mul,map_pow,
      restrictionValues,Matrix.cons_val_succ,Fin.reduceSucc,map_ofNat] <;> ring

def linkageIdeal (s : Side) (r ι : R) : Ideal (SeedRing r ι) :=
  Ideal.span (Set.range (fun j =>
    Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) (linkageGenerator s r j)))

theorem linkageGenerator_mem (s : Side) (r ι : R) (j : Fin 5) :
    Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) (linkageGenerator s r j) ∈
      linkageIdeal s r ι := Ideal.subset_span ⟨j,rfl⟩

theorem linkageIdeal_le_restrictionKernel (s : Side) (r ι : R) :
    linkageIdeal s r ι ≤ RingHom.ker (seedRestriction s r ι).toRingHom := by
  apply Ideal.span_le.mpr
  rintro z ⟨j,rfl⟩
  change seedRestriction s r ι
    (Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) (linkageGenerator s r j))=0
  rw [seedRestriction_mk]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  rw [substitution_linkageGenerator]
  apply Ideal.mem_span_pair.mpr
  exact ⟨curveGeneratorQuotient s r j,0,by simp⟩

def linkagePiece (s : Side) (r ι : R) (d ch : ℕ) : Submodule R (SeedPiece r ι d ch) :=
  ((linkageIdeal s r ι).restrictScalars R).comap (SeedPiece r ι d ch).subtype

theorem linkagePiece_le_restrictionKernel (s : Side) (r ι : R) (d ch : ℕ) :
    linkagePiece s r ι d ch ≤ LinearMap.ker (seedRestrictionPiece s r ι d ch) := by
  intro q hq
  apply LinearMap.mem_ker.mpr
  apply Subtype.ext
  change seedRestriction s r ι q.val=0
  exact linkageIdeal_le_restrictionKernel s r ι hq

def seedNormal [Nontrivial R] (r ι : R) : Poly R →ₗ[R] Poly R :=
  fullRemainderLinear (seedCubicCoefficients ι) (seedSexticCoefficients r ι)
    (seedCubicCoefficients_unit ι) (seedSexticCoefficients_unit r ι)

@[simp] theorem seedNormal_apply [Nontrivial R] (r ι : R) (p : Poly R) :
    seedNormal r ι p=fullRemainder (seedCubicCoefficients ι) (seedSexticCoefficients r ι)
      (seedCubicCoefficients_unit ι) (seedSexticCoefficients_unit r ι) p := rfl

theorem seedNormal_spec [Nontrivial R] (r ι : R) (p : Poly R) :
    FullStandard (seedNormal r ι p) ∧ ∃ a b,
      p=a*smoothH ι+b*seedG r+seedNormal r ι p := by
  obtain ⟨hs,a,b,hp⟩ := fullRemainder_spec (seedCubicCoefficients ι) (seedSexticCoefficients r ι)
    (seedCubicCoefficients_unit ι) (seedSexticCoefficients_unit r ι) p
  rw [seedCubicCoefficients_polynomial,seedSexticCoefficients_polynomial,smoothF] at hp
  refine ⟨hs,a+b*smoothK ι,b,?_⟩
  simp only [seedNormal_apply]
  linear_combination hp

theorem seedNormal_unique [Nontrivial R] (r ι : R) (p q a b : Poly R)
    (hq : FullStandard q) (hp : p=a*smoothH ι+b*seedG r+q) : q=seedNormal r ι p := by
  apply (existsUnique_full_invariant_representative (seedCubicCoefficients ι)
    (seedSexticCoefficients r ι) (seedCubicCoefficients_unit ι)
    (seedSexticCoefficients_unit r ι) p).choose_spec.2
  refine ⟨hq,a-b*smoothK ι,b,?_⟩
  rw [seedCubicCoefficients_polynomial,seedSexticCoefficients_polynomial,smoothF]
  linear_combination hp

theorem seedNormal_homogeneous [Nontrivial R] (r ι : R) {p : Poly R} {d : ℕ} {ch : ZMod 3}
    (hp : HG p (d,ch)) : HG (seedNormal r ι p) (d,ch) :=
  fullRemainder_preserves_grading (seedCubicCoefficients ι) (seedSexticCoefficients r ι)
    (seedCubicCoefficients_unit ι) (seedSexticCoefficients_unit r ι) hp

theorem seedNormal_eq_zero_iff [Nontrivial R] (r ι : R) (p : Poly R) :
    seedNormal r ι p=0 ↔ p ∈ equationsIdeal (smoothH ι) (smoothF r ι) := by
  rw [seedNormal_apply,fullRemainder_eq_zero_iff,seedCubicCoefficients_polynomial,seedSexticCoefficients_polynomial]

theorem seedNormal_map [Nontrivial R] {S : Type*} [CommRing S] [Nontrivial S]
    (φ : R →+* S) (r ι : R) (p : Poly R) :
    MvPolynomial.map φ (seedNormal r ι p)=seedNormal (φ r) (φ ι) (MvPolynomial.map φ p) := by
  simp only [seedNormal_apply]
  rw [fullRemainder_map]
  simp only [map_seedCubicCoefficients,map_seedSexticCoefficients]

@[simp] theorem map_linkageGenerator {S : Type*} [CommRing S]
    (φ : R →+* S) (s : Side) (r : R) (j : Fin 5) :
    MvPolynomial.map φ (linkageGenerator s r j)=linkageGenerator s (φ r) j := by
  cases s <;> fin_cases j <;>
    simp [linkageGenerator,CycleQ2SegreSeed.linkageE,CycleQ2SegreSeed.linkageEprime,
      Matrix.cons_val_succ,Fin.reduceSucc]

end CycleQ2SeedLinkageIdeals

#print axioms CycleQ2SeedLinkageIdeals.linkagePiece_le_restrictionKernel
#print axioms CycleQ2SeedLinkageIdeals.seedNormal_map
end
end

/- Component: continuation_3/LinkageComponentDecomposition.lean -/
section
/-! Elementary decomposition of the literal linkage ideal into its three
cubic-root components on the open where their common vertex is absent. -/

noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2LinkageComponentDecomposition

open CycleQ2SegreSeed
variable {R : Type*} [CommRing R]

def leftIdeal (a b c d : R) : Ideal R := Ideal.span (Set.range (linkageE a b c d))

def rootValues (ζ : R) : Fin 3 → R := ![1,ζ,ζ^2]

def componentGenerator (z a b c d : R) : Fin 2 → R := ![a-z*b,c+z^2*d]

def componentIdeal (z a b c d : R) : Ideal R :=
  Ideal.span (Set.range (componentGenerator z a b c d))

theorem leftGenerator_mem (a b c d : R) (j : Fin 5) :
    linkageE a b c d j ∈ leftIdeal a b c d := Ideal.subset_span ⟨j,rfl⟩

theorem componentGenerator_mem (z a b c d : R) (j : Fin 2) :
    componentGenerator z a b c d j ∈ componentIdeal z a b c d := Ideal.subset_span ⟨j,rfl⟩

theorem cube_eq_one (ζ : R) (hζ : ζ^2+ζ+1=0) : ζ^3=1 := by
  linear_combination (ζ-1)*hζ

theorem rootValues_cube (ζ : R) (hζ : ζ^2+ζ+1=0) (i : Fin 3) : rootValues ζ i^3=1 := by
  have h3 := cube_eq_one ζ hζ
  fin_cases i
  · simp [rootValues]
  · exact h3
  · change (ζ^2)^3=1
    calc
      (ζ^2)^3=(ζ^3)^2 := by ring
      _=1 := by rw [h3]; ring

theorem substituted_linkageE_zero (z b d : R) (hz : z^3=1) (j : Fin 5) :
    linkageE (z*b) b (-(z^2*d)) d j=0 := by
  have hz4 : z^4=z := by
    calc
      z^4=z^3*z := by ring
      _=z := by rw [hz]; ring
  have hz6 : z^6=1 := by
    calc
      z^6=(z^3)^2 := by ring
      _=1 := by rw [hz]; ring
  fin_cases j
  · change z*b*(-(z^2*d))+b*d=0
    ring_nf
    rw [hz]
    ring
  · change (z*b)^3-b^3=0
    ring_nf
    rw [hz]
    ring
  · change (z*b)^2*d+b^2*(-(z^2*d))=0
    ring
  · change z*b*d^2-b*(-(z^2*d))^2=0
    ring_nf
    rw [hz4]
    ring
  · change (-(z^2*d))^3+d^3=0
    ring_nf
    rw [hz6]
    ring

theorem leftIdeal_le_component (z a b c d : R) (hz : z^3=1) :
    leftIdeal a b c d ≤ componentIdeal z a b c d := by
  apply Ideal.span_le.mpr
  rintro x ⟨j,rfl⟩
  let J := componentIdeal z a b c d
  let f := Ideal.Quotient.mk J
  have ha : f a=f z*f b := by
    have h := Ideal.Quotient.eq_zero_iff_mem.mpr (componentGenerator_mem z a b c d 0)
    change f (a-z*b)=0 at h
    exact sub_eq_zero.mp (by simpa only [map_sub,map_mul] using h)
  have hc : f c= -(f z^2*f d) := by
    have h := Ideal.Quotient.eq_zero_iff_mem.mpr (componentGenerator_mem z a b c d 1)
    change f (c+z^2*d)=0 at h
    exact eq_neg_of_add_eq_zero_left (by simpa only [map_add,map_mul,map_pow] using h)
  have hz' : f z^3=1 := by simpa only [map_pow,map_one] using congrArg f hz
  have hm : f (linkageE a b c d j)=linkageE (f a) (f b) (f c) (f d) j := by
    fin_cases j <;> simp [linkageE,linkageP]
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change f (linkageE a b c d j)=0
  rw [hm,ha,hc]
  exact substituted_linkageE_zero (f z) (f b) (f d) hz' j

def productCombination (ζ a b c d : R) : Fin 2 → Fin 2 → Fin 2 → R :=
  ![![![linkageE a b c d 1,
       (a+(-ζ-1)*b)*linkageP a b c d+ζ*linkageE a b c d 2],
      ![(a+ζ*b)*linkageP a b c d+(-ζ-1)*linkageE a b c d 2,
       (c-d)*linkageP a b c d+linkageE a b c d 3]],
    ![![(a+b)*linkageP a b c d+linkageE a b c d 2,
       (c+(ζ+1)*d)*linkageP a b c d+ζ*linkageE a b c d 3],
      ![(c-ζ*d)*linkageP a b c d+(-ζ-1)*linkageE a b c d 3,
       linkageE a b c d 4]]]

theorem componentProduct_identity (ζ a b c d : R) (hζ : ζ^2+ζ+1=0)
    (i j k : Fin 2) :
    componentGenerator 1 a b c d i*componentGenerator ζ a b c d j*
      componentGenerator (ζ^2) a b c d k=productCombination ζ a b c d i j k := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp only [componentGenerator,one_pow,one_mul]
  · change (a-b)*(a-ζ*b)*(a-ζ^2*b)=a^3-b^3
    linear_combination b*(a-b)*(-a+b*ζ-b)*hζ
  · change (a-b)*(a-ζ*b)*(c+(ζ^2)^2*d)=
      (a+(-ζ-1)*b)*(a*c+b*d)+ζ*(a^2*d+b^2*c)
    linear_combination -d*(a-b)*(-a*ζ^2+a*ζ+b*ζ^3-b*ζ^2+b)*hζ
  · change (a-b)*(c+ζ^2*d)*(a-ζ^2*b)=
      (a+ζ*b)*(a*c+b*d)+(-ζ-1)*(a^2*d+b^2*c)
    linear_combination -(a-b)*(-a*d+b*c+b*d*ζ^2-b*d*ζ)*hζ
  · change (a-b)*(c+ζ^2*d)*(c+(ζ^2)^2*d)=(c-d)*(a*c+b*d)+(a*d^2-b*c^2)
    linear_combination d*(a-b)*(c+d*ζ^2-d)*(ζ^2-ζ+1)*hζ
  · change (c+d)*(a-ζ*b)*(a-ζ^2*b)=(a+b)*(a*c+b*d)+(a^2*d+b^2*c)
    linear_combination b*(c+d)*(-a+b*ζ-b)*hζ
  · change (c+d)*(a-ζ*b)*(c+(ζ^2)^2*d)=
      (c+(ζ+1)*d)*(a*c+b*d)+ζ*(a*d^2-b*c^2)
    linear_combination -d*(c+d)*(-a*ζ^2+a*ζ+b*ζ^3-b*ζ^2+b)*hζ
  · change (c+d)*(c+ζ^2*d)*(a-ζ^2*b)=(c-ζ*d)*(a*c+b*d)+(-ζ-1)*(a*d^2-b*c^2)
    linear_combination -(c+d)*(-a*d+b*c+b*d*ζ^2-b*d*ζ)*hζ
  · change (c+d)*(c+ζ^2*d)*(c+(ζ^2)^2*d)=c^3+d^3
    linear_combination d*(c+d)*(c+d*ζ^2-d)*(ζ^2-ζ+1)*hζ

theorem productCombination_mem (ζ a b c d : R) (i j k : Fin 2) :
    productCombination ζ a b c d i j k ∈ leftIdeal a b c d := by
  have hP : linkageP a b c d ∈ leftIdeal a b c d := leftGenerator_mem a b c d 0
  have hA := leftGenerator_mem a b c d 1
  have hB := leftGenerator_mem a b c d 2
  have hC := leftGenerator_mem a b c d 3
  have hD := leftGenerator_mem a b c d 4
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp only [productCombination,Matrix.cons_val_zero,Matrix.cons_val_one]
  · exact hA
  · exact (leftIdeal a b c d).add_mem ((leftIdeal a b c d).mul_mem_left _ hP)
      ((leftIdeal a b c d).mul_mem_left _ hB)
  · exact (leftIdeal a b c d).add_mem ((leftIdeal a b c d).mul_mem_left _ hP)
      ((leftIdeal a b c d).mul_mem_left _ hB)
  · exact (leftIdeal a b c d).add_mem ((leftIdeal a b c d).mul_mem_left _ hP) hC
  · exact (leftIdeal a b c d).add_mem ((leftIdeal a b c d).mul_mem_left _ hP) hB
  · exact (leftIdeal a b c d).add_mem ((leftIdeal a b c d).mul_mem_left _ hP)
      ((leftIdeal a b c d).mul_mem_left _ hC)
  · exact (leftIdeal a b c d).add_mem ((leftIdeal a b c d).mul_mem_left _ hP)
      ((leftIdeal a b c d).mul_mem_left _ hC)
  · exact hD

theorem component_product_le (ζ a b c d : R) (hζ : ζ^2+ζ+1=0) :
    componentIdeal 1 a b c d*componentIdeal ζ a b c d*componentIdeal (ζ^2) a b c d ≤
      leftIdeal a b c d := by
  unfold componentIdeal
  rw [Ideal.span_mul_span',Ideal.span_mul_span']
  apply Ideal.span_le.mpr
  rintro x ⟨y,⟨u,⟨i,rfl⟩,v,⟨j,rfl⟩,rfl⟩,w,⟨k,rfl⟩,rfl⟩
  change componentGenerator 1 a b c d i*componentGenerator ζ a b c d j*
    componentGenerator (ζ^2) a b c d k ∈ leftIdeal a b c d
  rw [componentProduct_identity ζ a b c d hζ]
  exact productCombination_mem ζ a b c d i j k

theorem components_sup_top (z w a b c d : R) (hz : z^3=1) (hw : w^3=1)
    (hzw : IsUnit (z-w)) (hzw2 : IsUnit (z^2-w^2))
    (hcover : leftIdeal a b c d ⊔ Ideal.span {b,d}=⊤) :
    componentIdeal z a b c d ⊔ componentIdeal w a b c d=⊤ := by
  let J := componentIdeal z a b c d ⊔ componentIdeal w a b c d
  have hb : b ∈ J := by
    apply (Ideal.unit_mul_mem_iff_mem J hzw).mp
    have h := J.sub_mem
      (show componentGenerator w a b c d 0 ∈ J from (le_sup_right : componentIdeal w a b c d ≤ J) (componentGenerator_mem w a b c d 0))
      (show componentGenerator z a b c d 0 ∈ J from (le_sup_left : componentIdeal z a b c d ≤ J) (componentGenerator_mem z a b c d 0))
    convert h using 1 <;> simp [componentGenerator] <;> ring
  have hd : d ∈ J := by
    apply (Ideal.unit_mul_mem_iff_mem J hzw2).mp
    have h := J.sub_mem
      (show componentGenerator z a b c d 1 ∈ J from (le_sup_left : componentIdeal z a b c d ≤ J) (componentGenerator_mem z a b c d 1))
      (show componentGenerator w a b c d 1 ∈ J from (le_sup_right : componentIdeal w a b c d ≤ J) (componentGenerator_mem w a b c d 1))
    convert h using 1 <;> simp [componentGenerator] <;> ring
  have hle : leftIdeal a b c d ⊔ Ideal.span {b,d} ≤ J := by
    apply sup_le
    · exact (leftIdeal_le_component z a b c d hz).trans le_sup_left
    · exact Ideal.span_le.mpr (by intro x hx; rcases hx with rfl | ⟨rfl⟩ <;> assumption)
  rw [hcover] at hle
  exact top_unique hle

theorem leftIdeal_eq_components (ζ a b c d : R) (hζ : ζ^2+ζ+1=0)
    (hunits : ∀ i j : Fin 3, i≠j → IsUnit (rootValues ζ i-rootValues ζ j) ∧
      IsUnit (rootValues ζ i^2-rootValues ζ j^2))
    (hcover : leftIdeal a b c d ⊔ Ideal.span {b,d}=⊤) :
    leftIdeal a b c d=
      (componentIdeal 1 a b c d ⊓ componentIdeal ζ a b c d) ⊓ componentIdeal (ζ^2) a b c d := by
  have h01 := components_sup_top (rootValues ζ 0) (rootValues ζ 1) a b c d
    (rootValues_cube ζ hζ 0) (rootValues_cube ζ hζ 1)
    (hunits 0 1 (by decide)).1 (hunits 0 1 (by decide)).2 hcover
  have h02 := components_sup_top (rootValues ζ 0) (rootValues ζ 2) a b c d
    (rootValues_cube ζ hζ 0) (rootValues_cube ζ hζ 2)
    (hunits 0 2 (by decide)).1 (hunits 0 2 (by decide)).2 hcover
  have h12 := components_sup_top (rootValues ζ 1) (rootValues ζ 2) a b c d
    (rootValues_cube ζ hζ 1) (rootValues_cube ζ hζ 2)
    (hunits 1 2 (by decide)).1 (hunits 1 2 (by decide)).2 hcover
  change componentIdeal 1 a b c d ⊔ componentIdeal ζ a b c d=⊤ at h01
  change componentIdeal 1 a b c d ⊔ componentIdeal (ζ^2) a b c d=⊤ at h02
  change componentIdeal ζ a b c d ⊔ componentIdeal (ζ^2) a b c d=⊤ at h12
  have hprod : componentIdeal 1 a b c d*componentIdeal ζ a b c d ⊔ componentIdeal (ζ^2) a b c d=⊤ := by
    rw [Ideal.mul_sup_eq_of_coprime_left h02,h12]
  apply le_antisymm
  · exact le_inf (le_inf (leftIdeal_le_component 1 a b c d (by simp))
      (leftIdeal_le_component ζ a b c d (cube_eq_one ζ hζ)))
      (leftIdeal_le_component (ζ^2) a b c d (rootValues_cube ζ hζ 2))
  · rw [←Ideal.mul_eq_inf_of_isCoprime (Ideal.isCoprime_iff_sup_eq.mpr h01),
      ←Ideal.mul_eq_inf_of_isCoprime (Ideal.isCoprime_iff_sup_eq.mpr hprod)]
    exact component_product_le ζ a b c d hζ

end CycleQ2LinkageComponentDecomposition

#print axioms CycleQ2LinkageComponentDecomposition.component_product_le
#print axioms CycleQ2LinkageComponentDecomposition.leftIdeal_eq_components
end
end

/- Component: continuation_3/cylinder_bridge/SeedFactorHomogeneous.lean -/
section
/-! # Original grading of the selected factor sections

These are the literal chosen sections of the incidence seed, with their
weighted degrees and cubic characters. The final projection identity is
applied before passing to the actual smooth quotient.
-/

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SeedFactorHomogeneous

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2SeedLinkageIdeals CycleQ2WeightedComponent

variable {R : Type*} [CommRing R]

private theorem regrade {p : Poly R} {a b : Grade} (hp : HG p a) (h : a=b) : HG p b := h ▸ hp

private lemma hx0 : HG (X 0 : Poly R) (1, 2) := isWeightedHomogeneous_X R fullGrading 0
private lemma hx1 : HG (X 1 : Poly R) (1, 2) := isWeightedHomogeneous_X R fullGrading 1
private lemma hx2 : HG (X 2 : Poly R) (1, 1) := isWeightedHomogeneous_X R fullGrading 2
private lemma hx3 : HG (X 3 : Poly R) (1, 0) := isWeightedHomogeneous_X R fullGrading 3
private lemma hw : HG (X 4 : Poly R) (2, 0) := isWeightedHomogeneous_X R fullGrading 4

private theorem leftCoeff0_homogeneous (i : Fin 3) :
    HG (CycleQ2SegreSeed.leftCoeff0 (X 0) (X 1) (X 2) (X 3) (X 4) i : Poly R) (6, 2) := by
  fin_cases i
  · exact (regrade (((hw.pow 2).neg.mul hx1).mul hx3) (by decide)).add
      (regrade ((hx1.pow 2).mul (hx2.pow 4)) (by decide))
  · exact ((regrade (hw.neg.mul (hx1.pow 4)) (by decide)).add
      (regrade ((hx0.pow 2).mul (hx2.pow 4)) (by decide))).add
      (regrade ((hx1.mul (hx2.pow 3)).mul (hx3.pow 2)) (by decide))
  · exact ((regrade (((hw.pow 2).neg.mul hx0).mul hx3) (by decide)).add
      (regrade ((hx1.pow 4).mul (hx3.pow 2)) (by decide))).add
      (regrade ((hx2.pow 2).mul (hx3.pow 4)) (by decide))

private theorem leftCoeff1_homogeneous (i : Fin 3) :
    HG (CycleQ2SegreSeed.leftCoeff1 (X 0) (X 1) (X 2) (X 3) (X 4) i : Poly R) (4, 0) := by
  fin_cases i
  · exact (regrade ((hx0.mul hx1).mul (hx2.pow 2)) (by decide)).sub
      (regrade ((hx0.mul hx2).mul (hx3.pow 2)) (by decide))
  · exact regrade (hx3.pow 4) (by decide)
  · exact regrade (hx3.pow 4) (by decide)

private theorem rightCoeff0_homogeneous (i : Fin 3) :
    HG (CycleQ2SegreSeed.rightCoeff0 (X 0) (X 1) (X 2) (X 3) (X 4) i : Poly R) (4, 0) := by
  fin_cases i
  · change HG (2 * (X 4 : Poly R) ^ 2 + 2 * X 4 * X 3 ^ 2) (4, 0)
    have h0 : HG ((C (2 : R)) * X 4 ^ 2) (4, 0) := regrade ((hw.pow 2).C_mul 2) (by decide)
    have h1 : HG ((C (2 : R)) * X 4 * X 3 ^ 2) (4, 0) :=
      regrade ((hw.C_mul 2).mul (hx3.pow 2)) (by decide)
    simpa only [map_ofNat] using h0.add h1
  · exact (regrade ((hw.mul hx0).mul hx2) (by decide)).add
      (regrade ((hx0.pow 2).mul (hx2.pow 2)) (by decide))
  · exact (((regrade ((hx0.mul (hx1.pow 2)).mul hx3) (by decide)).add
      (regrade ((hx1.mul hx2).mul (hx3.pow 2)) (by decide))).sub
      (regrade ((hx2.pow 3).mul hx3) (by decide))).add
      (regrade (hx3.pow 4) (by decide))

private theorem rightCoeff2_homogeneous (i : Fin 3) :
    HG (CycleQ2SegreSeed.rightCoeff2 (X 0) (X 1) (X 2) (X 3) (X 4) i : Poly R) (2, 0) := by
  fin_cases i
  · exact hw.add (regrade (hx3.pow 2) (by decide))
  · exact hw
  · exact isWeightedHomogeneous_zero _ _ _

private theorem rightCoeff3_homogeneous (i : Fin 3) :
    HG (CycleQ2SegreSeed.rightCoeff3 (X 0) (X 1) (X 2) (X 3) (X 4) i : Poly R) (2, 2) := by
  fin_cases i
  · exact isWeightedHomogeneous_zero _ _ _
  · exact regrade (hx0.mul hx3) (by decide)
  · exact isWeightedHomogeneous_zero _ _ _

private theorem baseRow0_homogeneous (r : R) (j : Fin 3) :
    HG (CycleQ2SegreSeed.baseRow0 (C r) (X 0) (X 1) (X 2) (X 3) (X 4) j) (8, 1) := by
  have ha : HG (X 0 ^ 2 : Poly R) (2, 1) := regrade (hx0.pow 2) (by decide)
  have hb : HG (C r * X 1 * X 3) (2, 2) := regrade ((hx1.C_mul r).mul hx3) (by decide)
  have hd : HG (X 2 ^ 2 : Poly R) (2, 2) := regrade (hx2.pow 2) (by decide)
  have hP := (regrade (ha.mul hw) (by decide : ((2,1) : Grade)+(2,0)=(4,1))).add
    (regrade (hb.mul hd) (by decide))
  have hQ := (regrade ((ha.pow 2).mul hb) (by decide : 2 • ((2,1) : Grade)+(2,2)=(6,1))).sub
    (regrade (hw.mul (hd.pow 2)) (by decide))
  have hT := (regrade (ha.mul (hb.pow 2)) (by decide : ((2,1) : Grade)+2 • (2,2)=(6,2))).add
    (regrade ((hw.pow 2).mul hd) (by decide))
  exact ((regrade (hP.mul (rightCoeff0_homogeneous j)) (by decide)).add
    (regrade (hQ.mul (rightCoeff2_homogeneous j)) (by decide))).add
    (regrade (hT.mul (rightCoeff3_homogeneous j)) (by decide))


def polynomialLeft (r : R) (i : Fin 3) : Poly R :=
  CycleQ2SegreSeed.leftSection (C r) (X 0) (X 1) (X 2) (X 3) (X 4) i

def polynomialRight (r : R) (j : Fin 3) : Poly R :=
  CycleQ2SegreSeed.rightSectionNumerator (C r) (X 0) (X 1) (X 2) (X 3) (X 4) j

def polynomialLinkage (r : R) : Poly R :=
  CycleQ2SegreSeed.seedP (C r) (X 0) (X 1) (X 2) (X 3) (X 4)

theorem polynomialLinkage_homogeneous (r : R) : HG (polynomialLinkage r) (4,1) :=
  linkageGenerator_homogeneous .left r 0

theorem polynomialLeft_homogeneous (r : R) (i : Fin 3) :
    HG (polynomialLeft r i) (10,0) := by
  have hP := polynomialLinkage_homogeneous r
  have hQ : HG ((X 0^2)^3-(C r*X 1*X 3)^3) (6,0) :=
    linkageGenerator_homogeneous .left r 1
  exact (regrade ((leftCoeff0_homogeneous i).mul hP) (by decide)).add
    (regrade ((leftCoeff1_homogeneous i).mul hQ) (by decide))

theorem polynomialRight_homogeneous (r : R) (j : Fin 3) :
    HG (polynomialRight r j) (8,1) := baseRow0_homogeneous r j

/-- Homogeneous projection of the literal factor numerator selects exactly
its degree-10 and degree-8 factor components, with the original characters. -/
theorem numerator_component (r : R) (V W : Fin 3 → Poly R) (d : Grade) (i j : Fin 3) :
    weightedHomogeneousComponent fullGrading (d+(18,1))
      (V i*polynomialRight r j+polynomialLeft r i*W j)=
      weightedHomogeneousComponent fullGrading (d+(10,0)) (V i)*polynomialRight r j+
      polynomialLeft r i*weightedHomogeneousComponent fullGrading (d+(8,1)) (W j) := by
  rw [map_add]
  have he : d+(18,1)=(d+(10,0))+(8,1) := by
    apply Prod.ext
    · change d.1+18=(d.1+10)+8
      omega
    · change d.2+1=(d.2+0)+1
      simp
  have he' : d+(18,1)=(10,0)+(d+(8,1)) := by
    apply Prod.ext
    · change d.1+18=10+(d.1+8)
      omega
    · change d.2+1=0+(d.2+1)
      simp
  rw [he,component_mul fullGrading (V i) (polynomialRight r j)
    (d+(10,0)) (8,1) (polynomialRight_homogeneous r j)]
  rw [← he,he',component_mul_left fullGrading (polynomialLeft r i) (W j)
    (10,0) (d+(8,1)) (polynomialLeft_homogeneous r i)]

end CycleQ2SeedFactorHomogeneous

#print axioms CycleQ2SeedFactorHomogeneous.polynomialLeft_homogeneous
#print axioms CycleQ2SeedFactorHomogeneous.polynomialRight_homogeneous
#print axioms CycleQ2SeedFactorHomogeneous.numerator_component
end
end

/- Component: continuation_3/SeedLinkagePrincipal.lean -/
section
/-!
# Actual linkage pairings and principal factor ideals on pivot charts

All ideals and sections are the literal seed definitions. Local
principality uses the checked regularity of the actual denominator.
-/

noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SeedLinkagePrincipal

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations CycleQ2IncidenceFirstOrder
  CycleQ2SegreTangentLocal CycleQ2SeedLinkageIdeals CycleQ2SeedLinkageRegular
  CycleQ2CurveRestriction CycleQ2SeedQuotientFiniteFree

variable {R : Type*} [CommRing R]

def quotientMap (r ι : R) : Poly R →+* SeedRing r ι := Ideal.Quotient.mk _

def leftSection (r ι : R) (i : Fin 3) : SeedRing r ι :=
  quotientMap r ι (CycleQ2SegreSeed.leftSection (C r) (X 0) (X 1) (X 2) (X 3) (X 4) i)

def rightSection (r ι : R) (j : Fin 3) : SeedRing r ι :=
  quotientMap r ι (CycleQ2SegreSeed.rightSectionNumerator (C r) (X 0) (X 1) (X 2) (X 3) (X 4) j)

def linkage (r ι : R) : SeedRing r ι :=
  quotientMap r ι (CycleQ2SegreSeed.seedP (C r) (X 0) (X 1) (X 2) (X 3) (X 4))

theorem quotient_seedG (r ι : R) : quotientMap r ι (seedG r)=0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact (smoothSeed_mem_iff_linkage r ι).mpr ⟨0,1,by simp⟩

theorem leftSection_mem (r ι : R) (i : Fin 3) :
    leftSection r ι i ∈ linkageIdeal .left r ι := by
  have h0 := linkageGenerator_mem .left r ι 0
  have h1 := linkageGenerator_mem .left r ι 1
  change quotientMap r ι (CycleQ2SegreSeed.seedP (C r) (X 0) (X 1) (X 2) (X 3) (X 4)) ∈ _ at h0
  change quotientMap r ι ((X 0^2)^3-(C r*X 1*X 3)^3) ∈ _ at h1
  unfold leftSection CycleQ2SegreSeed.leftSection
  rw [map_add,map_mul,map_mul]
  exact (linkageIdeal .left r ι).add_mem
    ((linkageIdeal .left r ι).mul_mem_left _ h0)
    ((linkageIdeal .left r ι).mul_mem_left _ h1)

theorem rightSection_mem (r ι : R) (j : Fin 3) :
    rightSection r ι j ∈ linkageIdeal .right r ι := by
  have h0 := linkageGenerator_mem .right r ι 0
  have h2 := linkageGenerator_mem .right r ι 2
  have h3 := linkageGenerator_mem .right r ι 3
  change quotientMap r ι (CycleQ2SegreSeed.linkageP (X 0^2) (C r*X 1*X 3) (X 4) (X 2^2)) ∈ _ at h0
  change quotientMap r ι ((X 0^2)^2*(C r*X 1*X 3)-X 4*(X 2^2)^2) ∈ _ at h2
  change quotientMap r ι ((X 0^2)*(C r*X 1*X 3)^2+(X 4)^2*(X 2^2)) ∈ _ at h3
  unfold rightSection CycleQ2SegreSeed.rightSectionNumerator CycleQ2SegreSeed.baseRow0
    CycleQ2SegreSeed.coreRight0
  rw [map_add,map_add,map_mul,map_mul,map_mul]
  exact (linkageIdeal .right r ι).add_mem
    ((linkageIdeal .right r ι).add_mem
      ((linkageIdeal .right r ι).mul_mem_right _ h0)
      ((linkageIdeal .right r ι).mul_mem_right _ h2))
    ((linkageIdeal .right r ι).mul_mem_right _ h3)

theorem generator_pairing (r ι : R) (i j : Fin 5) :
    quotientMap r ι (linkageGenerator .left r i) *
      quotientMap r ι (linkageGenerator .right r j) =
      linkage r ι * quotientMap r ι
        (CycleQ2SegreSeed.linkageQ (X 0^2) (C r*X 1*X 3) (X 4) (X 2^2) i j) := by
  change quotientMap r ι (CycleQ2SegreSeed.linkageE _ _ _ _ i)*
    quotientMap r ι (CycleQ2SegreSeed.linkageEprime _ _ _ _ j)=_
  rw [← map_mul,CycleQ2SegreSeed.linkage_pairing,map_add,map_mul,map_mul]
  change _+quotientMap r ι (seedG r)*_=_
  rw [quotient_seedG,zero_mul,add_zero]
  rfl

theorem ideals_pairing (r ι : R) :
    linkageIdeal .left r ι * linkageIdeal .right r ι ≤ Ideal.span {linkage r ι} := by
  unfold linkageIdeal
  rw [Ideal.span_mul_span']
  apply Ideal.span_le.mpr
  rintro x ⟨y,⟨i,rfl⟩,z,⟨j,rfl⟩,rfl⟩
  apply Ideal.mem_span_singleton.mpr
  refine ⟨quotientMap r ι
    (CycleQ2SegreSeed.linkageQ (X 0^2) (C r*X 1*X 3) (X 4) (X 2^2) i j), ?_⟩
  exact generator_pairing r ι i j

theorem selected_product (r ι : R) (i j : Fin 3) :
    leftSection r ι i*rightSection r ι j=linkage r ι*seedQuotientMatrix r ι i j := by
  unfold leftSection rightSection
  rw [← map_mul,CycleQ2SegreSeed.selected_product_identity,map_add,map_mul,map_mul]
  change _+quotientMap r ι (seedG r)*_=_
  rw [quotient_seedG,zero_mul,add_zero]
  rfl

section Maps
variable {S : Type*} [CommRing S]

theorem mapped_ideals_pairing (r ι : R) (φ : SeedRing r ι →+* S) :
    (linkageIdeal .left r ι).map φ * (linkageIdeal .right r ι).map φ ≤
      Ideal.span {φ (linkage r ι)} := by
  rw [← Ideal.map_mul]
  have h := Ideal.map_mono (f:=φ) (ideals_pairing r ι)
  simpa only [Ideal.map_span,Set.image_singleton] using h

theorem mapped_ideals_principal (r ι : R) (φ : SeedRing r ι →+* S)
    (hp : Function.Injective (fun x : S => φ (linkage r ι)*x))
    (i j : Fin 3) (hunit : IsUnit (φ (seedQuotientMatrix r ι i j))) :
    (linkageIdeal .left r ι).map φ=Ideal.span {φ (leftSection r ι i)} ∧
      (linkageIdeal .right r ι).map φ=Ideal.span {φ (rightSection r ι j)} := by
  apply CycleQ2LinkageIdealPrincipal.ideals_principal _ _ (φ (linkage r ι))
    (φ (leftSection r ι i)) (φ (rightSection r ι j))
    (φ (seedQuotientMatrix r ι i j)) hp hunit
    (Ideal.mem_map_of_mem φ (leftSection_mem r ι i))
    (Ideal.mem_map_of_mem φ (rightSection_mem r ι j))
  · simpa only [map_mul] using congrArg φ (selected_product r ι i j)
  · intro x hx y hy
    exact Ideal.mem_span_singleton.mp
      (mapped_ideals_pairing r ι φ (Ideal.mul_mem_mul hx hy))
end Maps

/-- On every localization chart with a unit literal matrix entry, both
actual factor ideals are generated by the corresponding chosen sections.
No regularity premise remains for the seed over a field. -/
theorem localized_ideals_principal {K : Type*} [Field K] (r ι : K) (hι : ι≠1)
    (M : Submonoid (SeedRing r ι)) (S : Type*) [CommRing S]
    [Algebra (SeedRing r ι) S] [IsLocalization M S]
    (i j : Fin 3) (hu : IsUnit (algebraMap (SeedRing r ι) S (seedQuotientMatrix r ι i j))) :
    (linkageIdeal .left r ι).map (algebraMap (SeedRing r ι) S)=
      Ideal.span {algebraMap (SeedRing r ι) S (leftSection r ι i)} ∧
    (linkageIdeal .right r ι).map (algebraMap (SeedRing r ι) S)=
      Ideal.span {algebraMap (SeedRing r ι) S (rightSection r ι j)} := by
  apply mapped_ideals_principal r ι (algebraMap (SeedRing r ι) S) _ i j hu
  exact CycleQ2LinkageIdealPrincipal.localization_mul_injective M S _
    (linkage_mul_injective r ι hι)

end CycleQ2SeedLinkagePrincipal

#print axioms CycleQ2SeedLinkagePrincipal.ideals_pairing
#print axioms CycleQ2SeedLinkagePrincipal.localized_ideals_principal
end
end

/- Component: continuation_3/SeedLinkageReflection.lean -/
section
/-! Sound sparse checks for actual five-variable normal forms of the literal
linkage sections.  Polynomial equality is proved over every ring of
characteristic109; finite computations do not assume any matrix rank. -/

set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SeedLinkageReflection

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2IncidenceJacobian CycleQ2CurveRestriction CycleQ2CurveRestrictionReflection
  CycleQ2SeedLinkageIdeals CycleQ2SparseModularPolynomial

def fullCoefficient (e : SourceTuple) : Sparse → ℕ
  | [] => 0
  | a::p => ((if a.1=e then a.2 else 0)+fullCoefficient e p)%109

def fullGood (d ch : ℕ) (p : Sparse) : Bool := p.all (fun a => sourceGood d ch a.1)

noncomputable section
variable {R : Type*} [CommRing R]

def fullValue [CharP R 109] (p : Sparse) : Poly R :=
  CycleQ2SparseModularPolynomial.eval (fun i : Fin 5 => X i) p

@[simp] theorem fullValue_nil [CharP R 109] : fullValue (R:=R) []=0 := rfl

@[simp] theorem fullValue_cons [CharP R 109] (a : Term) (p : Sparse) :
    fullValue (R:=R) (a::p)=termValue (fun i : Fin 5 => (X i : Poly R)) a+fullValue p := rfl

theorem sourceTupleExponent_injective : Function.Injective sourceTupleExponent := by
  intro e f h
  have h0 := congrArg (fun q : FullExponent => q 0) h
  have h1 := congrArg (fun q : FullExponent => q 1) h
  have h2 := congrArg (fun q : FullExponent => q 2) h
  have h3 := congrArg (fun q : FullExponent => q 3) h
  have h4 := congrArg (fun q : FullExponent => q 4) h
  exact Prod.ext h0 (Prod.ext h1 (Prod.ext h2 (Prod.ext h3 h4)))

theorem termValue_variables [CharP R 109] (a : Term) :
    termValue (fun i : Fin 5 => (X i : Poly R)) a =
      MvPolynomial.monomial (sourceTupleExponent a.1) (a.2:R) := by
  change (a.2 : Poly R)*sourceMonomial a.1=_
  rw [sourceMonomial_eq_monomial]
  rw [←map_natCast (C : R →+* Poly R) a.2,C_mul_monomial,mul_one]

theorem fullValue_coefficient [CharP R 109] (e : SourceTuple) (p : Sparse) :
    (fullValue (R:=R) p).coeff (sourceTupleExponent e)=(fullCoefficient e p:R) := by
  induction p with
  | nil => simp [fullCoefficient]
  | cons a p ih =>
    rw [fullValue_cons,coeff_add,termValue_variables,coeff_monomial,ih]
    by_cases he : a.1=e
    · simp [fullCoefficient,he,←CharP.cast_eq_mod R 109,Nat.cast_add]
    · have he' : sourceTupleExponent a.1≠sourceTupleExponent e :=
        fun h => he (sourceTupleExponent_injective h)
      simp only [fullCoefficient,if_neg he,if_neg he',←CharP.cast_eq_mod R 109,Nat.cast_add,Nat.cast_zero]

theorem fullGood_term [CharP R 109] (d ch : ℕ) (a : Term)
    (ha : sourceGood d ch a.1=true) :
    FullStandard (termValue (fun i : Fin 5 => (X i : Poly R)) a) ∧
      HG (termValue (fun i : Fin 5 => (X i : Poly R)) a) (d,(ch:ZMod 3)) := by
  have hm : termValue (fun i : Fin 5 => (X i : Poly R)) a=C (a.2:R)*sourceMonomial a.1 := by
    rw [termValue_variables,sourceMonomial_eq_monomial,C_mul_monomial,mul_one]
  rw [hm]
  have h := sourceGood_evaluation (R:=R) d ch a.1 ha
  exact ⟨fullStandard_C_mul h.1 _,h.2.C_mul _⟩

theorem fullGood_value [CharP R 109] (d ch : ℕ) (p : Sparse)
    (hp : fullGood d ch p=true) :
    FullStandard (fullValue (R:=R) p) ∧ HG (fullValue (R:=R) p) (d,(ch:ZMod 3)) := by
  induction p with
  | nil => exact ⟨by simp [FullStandard],(weightedHomogeneousSubmodule R fullGrading (d,(ch:ZMod 3))).zero_mem⟩
  | cons a p ih =>
    simp only [fullGood,List.all_cons,Bool.and_eq_true] at hp
    have ha := fullGood_term (R:=R) d ch a hp.1
    have hb := ih hp.2
    rw [fullValue_cons]
    exact ⟨fullStandard_add ha.1 hb.1,ha.2.add hb.2⟩

theorem checked_seedNormal [CharP R 109] [Nontrivial R]
    (r ι : R) (d ch : ℕ) (p n a b h g : Sparse)
    (hh : fullValue (R:=R) h=smoothH ι) (hg : fullValue (R:=R) g=seedG r)
    (hn : fullGood d ch n=true) (hc : checkZero (CycleQ2CurveRestrictionReflection.residual p n a b h g)=true) :
    seedNormal r ι (fullValue p)=fullValue n := by
  have hz := eval_eq_zero_of_check (fun i : Fin 5 => (X i : Poly R)) _ hc
  simp only [CycleQ2CurveRestrictionReflection.residual,CycleQ2SparseModularPolynomial.eval_add,
    CycleQ2SparseModularPolynomial.eval_neg,CycleQ2SparseModularPolynomial.eval_mul] at hz
  change fullValue p+ -(fullValue n+(fullValue a*fullValue h+fullValue b*fullValue g))=0 at hz
  rw [hh,hg] at hz
  symm
  apply seedNormal_unique r ι (fullValue p) (fullValue n) (fullValue a) (fullValue b)
  · exact (fullGood_value d ch n hn).1
  · linear_combination hz

end
end CycleQ2SeedLinkageReflection

#print axioms CycleQ2SeedLinkageReflection.checked_seedNormal
#print axioms CycleQ2SeedLinkageReflection.fullValue_coefficient
end

/- Component: continuation_3/SeedLinkageSections.lean -/
section
/-! Homogeneous monomial multiples of the literal linkage generators, and
the exact finite-minor criterion for their independence in the seed quotient. -/

set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SeedLinkageSections

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2CurveRestriction CycleQ2CurveRestrictionReflection CycleQ2SeedLinkageIdeals

abbrev SectionColumn := Fin 5 × SourceTuple

def tupleDegree (e : SourceTuple) : ℕ :=
  e.1+e.2.1+e.2.2.1+e.2.2.2.1+2*e.2.2.2.2

def tupleCharacter (e : SourceTuple) : ℕ := 2*e.1+2*e.2.1+e.2.2.1

def sectionGood (d ch : ℕ) (c : SectionColumn) : Bool :=
  decide (tupleDegree c.2+generatorDegree c.1=d ∧
    (tupleCharacter c.2+generatorCharacter c.1)%3=ch)

noncomputable section
variable {R : Type*} [CommRing R]

def sectionPolynomial (s : Side) (r : R) (c : SectionColumn) : Poly R :=
  sourceMonomial c.2*linkageGenerator s r c.1

@[simp] theorem map_sectionPolynomial {S : Type*} [CommRing S]
    (φ : R →+* S) (s : Side) (r : R) (c : SectionColumn) :
    MvPolynomial.map φ (sectionPolynomial s r c)=sectionPolynomial s (φ r) c := by
  simp only [sectionPolynomial,map_mul,map_sourceMonomial,map_linkageGenerator]

theorem sourceMonomial_grade (e : SourceTuple) :
    HG (sourceMonomial e : Poly R) (tupleDegree e,(tupleCharacter e:ZMod 3)) := by
  rw [sourceMonomial_eq_monomial]
  apply isWeightedHomogeneous_monomial
  rw [fullGrading_weight]
  rfl

theorem sectionPolynomial_homogeneous (s : Side) (r : R) (d ch : ℕ)
    (c : SectionColumn) (hc : sectionGood d ch c=true) :
    HG (sectionPolynomial s r c) (d,(ch:ZMod 3)) := by
  have h : tupleDegree c.2+generatorDegree c.1=d ∧
      (tupleCharacter c.2+generatorCharacter c.1)%3=ch := of_decide_eq_true hc
  have hg := (sourceMonomial_grade (R:=R) c.2).mul (linkageGenerator_homogeneous s r c.1)
  have he : (tupleDegree c.2,(tupleCharacter c.2:ZMod 3))+
      (generatorDegree c.1,(generatorCharacter c.1:ZMod 3))=(d,(ch:ZMod 3)) := by
    apply Prod.ext
    · exact h.1
    · have hh := congrArg (fun n : ℕ => (n:ZMod 3)) h.2
      simpa using hh
  exact he ▸ hg

def sectionClass (s : Side) (r ι : R) (d ch : ℕ) (c : SectionColumn)
    (hc : sectionGood d ch c=true) : SeedPiece r ι d ch :=
  ⟨Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) (sectionPolynomial s r c),
    Submodule.mem_map.mpr ⟨sectionPolynomial s r c,sectionPolynomial_homogeneous s r d ch c hc,rfl⟩⟩

def idealSection (s : Side) (r ι : R) (d ch : ℕ) (c : SectionColumn)
    (hc : sectionGood d ch c=true) : linkagePiece s r ι d ch :=
  ⟨sectionClass s r ι d ch c hc,by
    change Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι))
      (sectionPolynomial s r c) ∈ linkageIdeal s r ι
    rw [sectionPolynomial,map_mul]
    exact Ideal.mul_mem_left _ _ (linkageGenerator_mem s r ι c.1)⟩

def sectionCoefficient [Nontrivial R] (s : Side) (r ι : R)
    (row : SourceTuple) (c : SectionColumn) : R :=
  (seedNormal r ι (sectionPolynomial s r c)).coeff (sourceTupleExponent row)

theorem sectionCoefficient_map [Nontrivial R] {S : Type*} [CommRing S] [Nontrivial S]
    (φ : R →+* S) (s : Side) (r ι : R) (row : SourceTuple) (c : SectionColumn) :
    φ (sectionCoefficient s r ι row c)=sectionCoefficient s (φ r) (φ ι) row c := by
  unfold sectionCoefficient
  rw [←coeff_map,seedNormal_map,map_sectionPolynomial]

section Field
variable {K : Type*} [Field K]

theorem idealSections_independent_of_minor (s : Side) (r ι : K) (d ch n : ℕ)
    (rows : Fin n → SourceTuple) (columns : Fin n → SectionColumn)
    (hcolumns : ∀ j, sectionGood d ch (columns j)=true)
    (hdet : Matrix.det (fun i j : Fin n => sectionCoefficient s r ι (rows i) (columns j))≠0) :
    LinearIndependent K (fun j => idealSection s r ι d ch (columns j) (hcolumns j)) := by
  classical
  let A : Matrix (Fin n) (Fin n) K := fun i j => sectionCoefficient s r ι (rows i) (columns j)
  have hA : Function.Injective A.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr
      (A.isUnit_iff_isUnit_det.mpr ((isUnit_iff_ne_zero).mpr hdet))
  refine (Fintype.linearIndependent_iff (R:=K)
    (v:=fun j => idealSection s r ι d ch (columns j) (hcolumns j))).mpr ?_
  intro v hv j
  let P : Poly K := ∑ k, v k • sectionPolynomial s r (columns k)
  have hz : Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) P=0 := by
    have h := congrArg (fun q : linkagePiece s r ι d ch => q.val.val) hv
    change (Ideal.Quotient.mkₐ K (equationsIdeal (smoothH ι) (smoothF r ι))) P=0
    simp only [P,map_sum,map_smul]
    simpa only [Submodule.coe_sum,Submodule.coe_smul,Submodule.coe_zero,
      idealSection,sectionClass,Ideal.Quotient.mkₐ_eq_mk] using h
  have hn : seedNormal r ι P=0 :=
    (seedNormal_eq_zero_iff r ι P).mpr (Ideal.Quotient.eq_zero_iff_mem.mp hz)
  have hAv : A.mulVec v=0 := by
    funext i
    have hcoeff := congrArg (fun p : Poly K => p.coeff (sourceTupleExponent (rows i))) hn
    have hsum : (seedNormal r ι P).coeff (sourceTupleExponent (rows i))=A.mulVec v i := by
      simp only [P,map_sum,map_smul,coeff_sum,coeff_smul,RingHom.id_apply,
        Matrix.mulVec,dotProduct,A,sectionCoefficient]
      apply Finset.sum_congr rfl
      intro k hk
      exact mul_comm _ _
    rw [hsum,coeff_zero] at hcoeff
    exact hcoeff
  have hv0 : v=0 := hA (by simpa using hAv)
  exact congrFun hv0 j

theorem linkagePiece_rank_lower_bound (s : Side) (r ι : K) (d ch n : ℕ) (hch : ch<3)
    (rows : Fin n → SourceTuple) (columns : Fin n → SectionColumn)
    (hcolumns : ∀ j, sectionGood d ch (columns j)=true)
    (hdet : Matrix.det (fun i j : Fin n => sectionCoefficient s r ι (rows i) (columns j))≠0) :
    n ≤ Module.finrank K (linkagePiece s r ι d ch) := by
  letI : FiniteDimensional K (SeedPiece r ι d ch) :=
    Module.Finite.of_basis (seedPieceBasis r ι d ch hch)
  simpa using (idealSections_independent_of_minor s r ι d ch n rows columns hcolumns hdet).fintype_card_le_finrank

end Field
end
end CycleQ2SeedLinkageSections

#print axioms CycleQ2SeedLinkageSections.idealSections_independent_of_minor
#print axioms CycleQ2SeedLinkageSections.linkagePiece_rank_lower_bound
end

/- Component: continuation_3/SeedQuotientGrading.lean -/
section
/-! # Agreement of the coordinate grading with the polynomial grading -/

noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SeedQuotientGrading

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2SegreTangentLocal CycleQ2SeedQuotientFiniteFree CycleQ2SeedCechThreeOpen
  CycleQ2SeedCechLocalization CycleQ2SeedCechLocalizedBasis CycleQ2SeedCechLinearCoordinates
  CycleQ2SeedCechRestrictions

variable (R : Type*) [CommRing R]

def mergeExponent (e : Fin 2 →₀ ℕ) (d : Fin 3 →₀ ℕ) : FullExponent :=
  Finsupp.equivFunOnFinite.symm ![e 0, d 0, d 1, d 2, e 1]

lemma coeff_curry (p : AddMonoidAlgebra R ((Fin 2 →₀ ℕ) × (Fin 3 →₀ ℕ)))
    (e : Fin 2 →₀ ℕ) (d : Fin 3 →₀ ℕ) :
    ((AddMonoidAlgebra.curryAlgEquiv R p).coeff e).coeff d = p.coeff (e, d) := rfl

lemma regroup_coeff_coeff (p : Poly R) (e : Fin 2 →₀ ℕ) (d : Fin 3 →₀ ℕ) :
    ((regroup R p).coeff e).coeff d = p.coeff (mergeExponent e d) := by
  change ((AddMonoidAlgebra.curryAlgEquiv R
    (AddMonoidAlgebra.domCongr R R Finsupp.sumFinsuppAddEquivProdFinsupp
      (renameEquiv R splitIndex p))).coeff e).coeff d = _
  rw [coeff_curry, AddMonoidAlgebra.coeff_domCongr]
  have heq : Finsupp.sumFinsuppAddEquivProdFinsupp.symm (e, d) =
      (mergeExponent e d).mapDomain splitIndex := by
    ext z
    obtain ⟨j, rfl⟩ := splitIndex.surjective z
    rw [Finsupp.mapDomain_apply splitIndex.injective]
    fin_cases j <;> rfl
  rw [heq]
  exact coeff_rename_mapDomain splitIndex splitIndex.injective p (mergeExponent e d)

def outerExponent (ab : ShiftIndex) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 ab.1.val + Finsupp.single 1 ab.2.val

lemma regroup_standard {p : Poly R} (hp : FullStandard p) : Standard (regroup R p) := by
  intro e he
  obtain ⟨d, hd⟩ := exists_coeff_ne_zero (MvPolynomial.mem_support_iff.mp he)
  rw [regroup_coeff_coeff] at hd
  have hb := hp (mergeExponent e d) (MvPolynomial.mem_support_iff.mpr hd)
  exact ⟨hb.1, hb.2⟩

lemma nested_reduced [Nontrivial R] (r ι : R) {p : Nested R} (hp : Standard p) :
    Reduced auxiliaryOrder (nestedH R ι) (nestedG R r) p := by
  intro e he
  rw [(nestedH_leading R ι).1, (nestedG_leading R r).1,
    single_three_le_iff, single_three_le_iff]
  exact ⟨Nat.not_le_of_lt (hp e he).1, Nat.not_le_of_lt (hp e he).2⟩

lemma quotientBasis_repr_reduced {A σ : Type*} [CommRing A]
    (m : MonomialOrder σ) (h F p : MvPolynomial σ A)
    (hh : m.Monic h) (hF : m.Monic F)
    (hcop : ∀ i, m.degree h i = 0 ∨ m.degree F i = 0)
    (hp : Reduced m h F p) (d : reducedExponents m h F) :
    (quotientBasis m h F hh hF hcop).repr (Ideal.Quotient.mk (equationsIdeal h F) p) d =
      p.coeff d.val := by
  let E := reducedQuotientEquiv m h F hh hF hcop
  have he : E ⟨p, hp⟩ = Ideal.Quotient.mk (equationsIdeal h F) p := rfl
  change (MvPolynomial.basisRestrictSupport A (reducedExponents m h F)).repr
    (E.symm (Ideal.Quotient.mk (equationsIdeal h F) p)) d = _
  rw [← he, LinearEquiv.symm_apply_apply]
  rfl

lemma nestedBasis_repr_standard [Nontrivial R] (r ι : R) (p : Nested R)
    (hp : Standard p) (ab : ShiftIndex) :
    (nestedBasis R r ι).repr (Ideal.Quotient.mk (nestedIdeal R r ι) p) ab =
      p.coeff (outerExponent ab) := by
  unfold nestedBasis
  erw [Module.Basis.repr_reindex_apply,
    quotientBasis_repr_reduced auxiliaryOrder (nestedH R ι) (nestedG R r) p
      (nestedH_leading R ι).2 (nestedG_leading R r).2 (nested_coprime R r ι)
      (nested_reduced R r ι hp)]
  rfl

lemma seedBasis_repr_standard [Nontrivial R] (r ι : R) (p : Poly R)
    (hp : FullStandard p) (ab : ShiftIndex) :
    (seedBasis R r ι).repr (Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) p) ab =
      (regroup R p).coeff (outerExponent ab) := by
  change (nestedBasis R r ι).repr
    (Ideal.Quotient.mk (nestedIdeal R r ι) (regroup R p)) ab = _
  exact nestedBasis_repr_standard R r ι (regroup R p) (regroup_standard R hp) ab

lemma seedBasis_repr_standard_coeff [Nontrivial R] (r ι : R) (p : Poly R)
    (hp : FullStandard p) (ab : ShiftIndex) (d : Fin 3 →₀ ℕ) :
    ((seedBasis R r ι).repr
      (Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) p) ab).coeff d =
        p.coeff (mergeExponent (outerExponent ab) d) := by
  rw [seedBasis_repr_standard R r ι p hp, regroup_coeff_coeff]

def signedGrade (g : Grade) : LaurentGrade := ((g.1 : ℤ), g.2)

theorem mergeExponent_grade (ab : ShiftIndex) (d : Fin 3 →₀ ℕ) :
    signedGrade (Finsupp.weight fullGrading (mergeExponent (outerExponent ab) d)) =
      shiftedGrade ab (castExponent d) := by
  rw [fullGrading_weight]
  apply Prod.ext <;>
    simp [signedGrade, fullDegree, mergeExponent, outerExponent, shiftedGrade,
      Fin.sum_univ_succ, castExponent] <;> ring

@[simp] theorem baseToLaurent_coeff_cast (p : Base R) (d : Fin 3 →₀ ℕ) :
    (baseToLaurent R p).coeff (castExponent d) = p.coeff d :=
  Finsupp.mapDomain_apply castExponent_injective _ _

lemma standard_seedCoordinates_homogeneous [Nontrivial R] (r ι : R)
    (p : Poly R) (g : Grade) (hs : FullStandard p) (hp : HG p g) (ab : ShiftIndex) :
    HasGrade ab (signedGrade g)
      (baseToLaurent R ((seedBasis R r ι).repr
        (Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) p) ab)) := by
  intro e he
  by_contra hne
  have hpos : ∀ i, 0 ≤ e i := by
    intro i
    by_contra hi
    exact hne (baseToLaurent_hasPoles R _ e i (by simp) (lt_of_not_ge hi))
  obtain ⟨d, rfl⟩ := (mem_range_castExponent e).mpr hpos
  rw [baseToLaurent_coeff_cast, seedBasis_repr_standard_coeff R r ι p hs] at hne
  have hh := congrArg signedGrade (hp hne)
  rw [mergeExponent_grade] at hh
  exact he hh

/-- Original five-variable homogeneity gives exactly the declared shifts in
all nine canonical quotient coordinates. -/
theorem seedCoordinates_homogeneous [Nontrivial R] (r ι : R)
    (p : Poly R) (g : Grade) (hp : HG p g) (ab : ShiftIndex) :
    HasGrade ab (signedGrade g)
      (baseToLaurent R ((seedBasis R r ι).repr
        (Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) p) ab)) := by
  let N := fullRemainder (seedCubicCoefficients ι) (seedSexticCoefficients r ι)
    (seedCubicCoefficients_unit ι) (seedSexticCoefficients_unit r ι) p
  obtain ⟨hN, a, b, hab⟩ := fullRemainder_spec
    (seedCubicCoefficients ι) (seedSexticCoefficients r ι)
    (seedCubicCoefficients_unit ι) (seedSexticCoefficients_unit r ι) p
  have hQ : Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) p =
      Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) N := by
    apply Ideal.Quotient.eq.mpr
    apply Ideal.mem_span_pair.mpr
    refine ⟨a, b, ?_⟩
    simp only [seedCubicCoefficients_polynomial, seedSexticCoefficients_polynomial] at hab
    exact (sub_eq_iff_eq_add.mpr hab).symm
  have hNg : HG N g := fullRemainder_preserves_grading
    (seedCubicCoefficients ι) (seedSexticCoefficients r ι)
    (seedCubicCoefficients_unit ι) (seedSexticCoefficients_unit r ι) hp
  rw [hQ]
  exact standard_seedCoordinates_homogeneous R r ι N g hN hNg ab

theorem localized_polynomial_homogeneous [Nontrivial R] (r ι : R)
    (s : Finset (Fin 3)) (p : Poly R) (g : Grade) (hp : HG p g) (ab : ShiftIndex) :
    HasGrade ab (signedGrade g)
      (localizedCoordinates R r ι s (algebraMap (SeedRing r ι) (SeedLocal R r ι s)
        (Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) p)) ab) := by
  rw [localizedCoordinates_algebraMap]
  exact seedCoordinates_homogeneous R r ι p g hp ab

theorem signedGrade_injective : Function.Injective signedGrade := by
  intro a b hab
  apply Prod.ext
  · exact Nat.cast_injective (congrArg Prod.fst hab)
  · exact congrArg (fun g : LaurentGrade ↦ g.2) hab

/-- The original polynomial grading, allowing a signed target degree. -/
def SignedHomogeneous (p : Poly R) (g : LaurentGrade) : Prop :=
  ∀ e, p.coeff e ≠ 0 → signedGrade (Finsupp.weight fullGrading e) = g

theorem signedHomogeneous_iff (p : Poly R) (g : Grade) :
    SignedHomogeneous R p (signedGrade g) ↔ HG p g := by
  constructor
  · intro hp e he
    exact signedGrade_injective (hp e he)
  · intro hp e he
    exact congrArg signedGrade (hp he)

theorem seedCoordinates_signedHomogeneous [Nontrivial R] (r ι : R)
    (p : Poly R) (g : LaurentGrade) (hp : SignedHomogeneous R p g) (ab : ShiftIndex) :
    HasGrade ab g (baseToLaurent R ((seedBasis R r ι).repr
      (Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) p) ab)) := by
  by_cases hz : p = 0
  · subst p
    intro e he
    simp
  · obtain ⟨e, he⟩ := exists_coeff_ne_zero hz
    have hg := hp e he
    have hh : HG p (Finsupp.weight fullGrading e) := by
      apply (signedHomogeneous_iff R p _).mp
      exact hg.symm ▸ hp
    exact hg ▸ seedCoordinates_homogeneous R r ι p _ hh ab

/-- The standard normal form is homogeneous exactly when all nine
canonical coefficient polynomials have the corresponding shifted grades. -/
theorem standard_signedHomogeneous_iff_coordinates [Nontrivial R] (r ι : R)
    (p : Poly R) (g : LaurentGrade) (hs : FullStandard p) :
    SignedHomogeneous R p g ↔
      ∀ ab, HasGrade ab g (baseToLaurent R ((seedBasis R r ι).repr
        (Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) p) ab)) := by
  constructor
  · intro hp ab
    exact seedCoordinates_signedHomogeneous R r ι p g hp ab
  · intro hc e he
    have hb := hs e (MvPolynomial.mem_support_iff.mpr he)
    let ab : ShiftIndex := (⟨e 0, hb.1⟩, ⟨e 4, hb.2⟩)
    let d : Fin 3 →₀ ℕ := Finsupp.equivFunOnFinite.symm ![e 1, e 2, e 3]
    have heq : mergeExponent (outerExponent ab) d = e := by
      ext i
      fin_cases i <;> simp [mergeExponent, outerExponent, ab, d]
    rw [← heq, mergeExponent_grade]
    by_contra hg
    have hz := hc ab (castExponent d) hg
    rw [baseToLaurent_coeff_cast, seedBasis_repr_standard_coeff R r ι p hs] at hz
    exact he (heq ▸ hz)

/-- Every homogeneous quotient class has a genuinely homogeneous polynomial
representative, with no grading assumption on a chosen initial lift. -/
theorem exists_signed_homogeneous_representative [Nontrivial R] (r ι : R)
    (q : SeedRing r ι) (g : LaurentGrade)
    (hq : ∀ ab, HasGrade ab g (baseToLaurent R ((seedBasis R r ι).repr q ab))) :
    ∃ p : Poly R, FullStandard p ∧ SignedHomogeneous R p g ∧
      Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) p = q := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
  let N := fullRemainder (seedCubicCoefficients ι) (seedSexticCoefficients r ι)
    (seedCubicCoefficients_unit ι) (seedSexticCoefficients_unit r ι) p
  obtain ⟨hN, a, b, hab⟩ := fullRemainder_spec
    (seedCubicCoefficients ι) (seedSexticCoefficients r ι)
    (seedCubicCoefficients_unit ι) (seedSexticCoefficients_unit r ι) p
  have hQ : Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) p =
      Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) N := by
    apply Ideal.Quotient.eq.mpr
    apply Ideal.mem_span_pair.mpr
    refine ⟨a, b, ?_⟩
    simp only [seedCubicCoefficients_polynomial, seedSexticCoefficients_polynomial] at hab
    exact (sub_eq_iff_eq_add.mpr hab).symm
  refine ⟨N, hN, ?_, hQ.symm⟩
  apply (standard_signedHomogeneous_iff_coordinates R r ι N g hN).mpr
  rw [← hQ]
  exact hq

/-- Signed degree and cubic character of a Laurent monomial in the base variables. -/
def baseGrade : LaurentExponent →+ LaurentGrade where
  toFun e := (∑ i, e i, (2 * e 0 + e 1 : ℤ))
  map_zero' := by simp
  map_add' e f := by
    apply Prod.ext <;> simp [Finset.sum_add_distrib] <;> ring

theorem shiftedGrade_add (ab : ShiftIndex) (e f : LaurentExponent) :
    shiftedGrade ab (e + f) = shiftedGrade ab e + baseGrade f := by
  apply Prod.ext <;> simp [shiftedGrade, baseGrade, Finset.sum_add_distrib] <;> ring

theorem hasGrade_mul_T (ab : ShiftIndex) (g : LaurentGrade) (e : LaurentExponent)
    (p : Laurent (R := R)) (hp : HasGrade ab g p) :
    HasGrade ab (g + baseGrade e) (p * T R e) := by
  intro f hf
  rw [coeff_mul_T]
  apply hp
  intro hh
  apply hf
  calc
    shiftedGrade ab f = shiftedGrade ab ((f - e) + e) := by rw [sub_add_cancel]
    _ = shiftedGrade ab (f - e) + baseGrade e := shiftedGrade_add ab _ _
    _ = g + baseGrade e := by rw [hh]

theorem coordinates_fraction [Nontrivial R] (r ι : R) (s : Finset (Fin 3))
    (q : SeedLocal R r ι s) (num : SeedRing r ι) (n : ℕ)
    (h : q * algebraMap (SeedRing r ι) (SeedLocal R r ι s)
      (algebraMap (Base R) (SeedRing r ι) (baseProduct R s ^ n)) =
      algebraMap (SeedRing r ι) (SeedLocal R r ι s) num) (ab : ShiftIndex) :
    baseToLaurent R ((seedBasis R r ι).repr num ab) =
      localizedCoordinates R r ι s q ab * T R (n • openExponent s) := by
  have hh := congrArg (fun z ↦ localizedCoordinates R r ι s z ab) h
  rw [coordinates_mul_base, localizedCoordinates_algebraMap] at hh
  simp only [map_pow, baseToLaurent_baseProduct, T_pow] at hh
  exact hh.symm.trans (mul_comm _ _)

/-- The coordinate definition of a graded local section agrees with an
actual fraction having a polynomial numerator of the required original grade. -/
theorem localized_homogeneous_iff_fraction [Nontrivial R] (r ι : R)
    (s : Finset (Fin 3)) (q : SeedLocal R r ι s) (g : LaurentGrade) :
    (∀ ab, HasGrade ab g (localizedCoordinates R r ι s q ab)) ↔
      ∃ (n : ℕ) (p : Poly R),
        SignedHomogeneous R p (g + baseGrade (n • openExponent s)) ∧
        q * algebraMap (SeedRing r ι) (SeedLocal R r ι s)
          (algebraMap (Base R) (SeedRing r ι) (baseProduct R s ^ n)) =
          algebraMap (SeedRing r ι) (SeedLocal R r ι s)
            (Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) p) := by
  constructor
  · intro hq
    obtain ⟨n, num, hn⟩ := IsLocalization.Away.surj
      (algebraMap (Base R) (SeedRing r ι) (baseProduct R s)) q
    have hn' : q * algebraMap (SeedRing r ι) (SeedLocal R r ι s)
        (algebraMap (Base R) (SeedRing r ι) (baseProduct R s ^ n)) =
        algebraMap (SeedRing r ι) (SeedLocal R r ι s) num := by
      simpa only [map_pow] using hn
    have hnum (ab : ShiftIndex) :
        HasGrade ab (g + baseGrade (n • openExponent s))
          (baseToLaurent R ((seedBasis R r ι).repr num ab)) := by
      rw [coordinates_fraction R r ι s q num n hn' ab]
      exact hasGrade_mul_T R ab g _ _ (hq ab)
    obtain ⟨p, _, hp, hpn⟩ := exists_signed_homogeneous_representative R r ι num _ hnum
    refine ⟨n, p, hp, ?_⟩
    simpa only [hpn] using hn'
  · rintro ⟨n, p, hp, hfrac⟩ ab
    have hh := coordinates_fraction R r ι s q
      (Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) p) n hfrac ab
    have hnum := seedCoordinates_signedHomogeneous R r ι p _ hp ab
    have hrep : localizedCoordinates R r ι s q ab =
        baseToLaurent R ((seedBasis R r ι).repr
          (Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) p) ab) *
          T R (-(n • openExponent s)) := by
      have hm := congrArg (fun z ↦ z * T R (-(n • openExponent s))) hh
      simpa only [mul_assoc, T_mul, add_neg_cancel, T_zero, mul_one] using hm.symm
    rw [hrep]
    have hz := hasGrade_mul_T R ab _ (-(n • openExponent s)) _ hnum
    simpa only [map_neg, add_neg_cancel_right] using hz

end CycleQ2SeedQuotientGrading

#print axioms CycleQ2SeedQuotientGrading.localized_polynomial_homogeneous

#print axioms CycleQ2SeedQuotientGrading.localized_homogeneous_iff_fraction
end
end

/- Component: continuation_3/cylinder_bridge/SegreLinkageDuality.lean -/
section
/-! The literal regular linkage pairing is perfect wherever the actual
matrix entries generate the unit ideal.  The inverse is an explicit finite
sum coming from that unit-ideal identity; no duality or invertibility of
the two factor ideals is assumed. -/

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SegreLinkageDuality
open Matrix CycleQ2SegreFactorSequence

variable {A : Type*} [CommRing A] (F : FactorData A)

def leftElement (i : Fin 3) : F.leftIdeal := ⟨F.left i,F.left_mem i⟩
def rightElement (j : Fin 3) : F.rightIdeal := ⟨F.right j,F.right_mem j⟩

theorem pair_divisible (x : F.leftIdeal) (y : F.rightIdeal) :
    F.linkage ∣ (x:A)*(y:A) :=
  Ideal.mem_span_singleton.mp (F.ideals_product (Ideal.mul_mem_mul x.property y.property))

def pairValue (x : F.leftIdeal) (y : F.rightIdeal) : A := (pair_divisible F x y).choose

theorem linkage_pair (x : F.leftIdeal) (y : F.rightIdeal) :
    F.linkage*pairValue F x y=(x:A)*(y:A) :=
  (pair_divisible F x y).choose_spec.symm

def pairing : F.rightIdeal →ₗ[A] (F.leftIdeal →ₗ[A] A) where
  toFun y :=
    { toFun := fun x => pairValue F x y
      map_add' x z := by
        apply F.regular
        change F.linkage*pairValue F (x+z) y=F.linkage*(pairValue F x y+pairValue F z y)
        rw [mul_add,linkage_pair,linkage_pair,linkage_pair]
        change ((x:A)+(z:A))*(y:A)=(x:A)*(y:A)+(z:A)*(y:A)
        ring
      map_smul' c x := by
        apply F.regular
        change F.linkage*pairValue F (c • x) y=F.linkage*(c*pairValue F x y)
        rw [show F.linkage*(c*pairValue F x y)=c*(F.linkage*pairValue F x y) by ring,
          linkage_pair,linkage_pair]
        change (c*(x:A))*(y:A)=c*((x:A)*(y:A))
        ring }
  map_add' y z := by
    ext x
    apply F.regular
    change F.linkage*pairValue F x (y+z)=F.linkage*(pairValue F x y+pairValue F x z)
    rw [mul_add,linkage_pair,linkage_pair,linkage_pair]
    change (x:A)*((y:A)+(z:A))=(x:A)*(y:A)+(x:A)*(z:A)
    ring
  map_smul' c y := by
    ext x
    apply F.regular
    change F.linkage*pairValue F x (c • y)=F.linkage*(c*pairValue F x y)
    rw [show F.linkage*(c*pairValue F x y)=c*(F.linkage*pairValue F x y) by ring,
      linkage_pair,linkage_pair]
    change (x:A)*(c*(y:A))=c*((x:A)*(y:A))
    ring

theorem pairing_selected (i j : Fin 3) :
    pairing F (rightElement F j) (leftElement F i)=F.matrix i j := by
  apply F.regular
  exact (linkage_pair F (leftElement F i) (rightElement F j)).trans (F.product i j)

theorem exists_weights :
    ∃ ξ : Fin 3 × Fin 3 → A, ∑ q, ξ q*F.matrix q.1 q.2=1 := by
  apply Ideal.mem_span_range_iff_exists_fun.mp
  rw [F.entries_generate]
  exact Submodule.mem_top

def weights : Fin 3 × Fin 3 → A := (exists_weights F).choose

theorem weights_sum : ∑ q, weights F q*F.matrix q.1 q.2=1 :=
  (exists_weights F).choose_spec

theorem left_reconstruction (x : F.leftIdeal) :
    (x:A)=∑ q, (weights F q*pairing F (rightElement F q.2) x)*F.left q.1 := by
  apply F.regular
  calc
    F.linkage*(x:A)=(∑ q, weights F q*F.matrix q.1 q.2)*(F.linkage*(x:A)) := by
      rw [weights_sum,one_mul]
    _=∑ q, (weights F q*F.matrix q.1 q.2)*(F.linkage*(x:A)) := by rw [Finset.sum_mul]
    _=∑ q, F.linkage*((weights F q*pairing F (rightElement F q.2) x)*F.left q.1) := by
      apply Finset.sum_congr rfl
      intro q _
      have hpair := linkage_pair F x (rightElement F q.2)
      change F.linkage*pairing F (rightElement F q.2) x=(x:A)*F.right q.2 at hpair
      linear_combination
        -weights F q*(x:A)*(F.product q.1 q.2)-weights F q*F.left q.1*hpair
    _=F.linkage*(∑ q, (weights F q*pairing F (rightElement F q.2) x)*F.left q.1) :=
      (Finset.mul_sum ..).symm

theorem right_reconstruction (y : F.rightIdeal) :
    (y:A)=∑ q, (weights F q*pairing F y (leftElement F q.1))*F.right q.2 := by
  apply F.regular
  calc
    F.linkage*(y:A)=(∑ q, weights F q*F.matrix q.1 q.2)*(F.linkage*(y:A)) := by
      rw [weights_sum,one_mul]
    _=∑ q, (weights F q*F.matrix q.1 q.2)*(F.linkage*(y:A)) := by rw [Finset.sum_mul]
    _=∑ q, F.linkage*((weights F q*pairing F y (leftElement F q.1))*F.right q.2) := by
      apply Finset.sum_congr rfl
      intro q _
      have hpair := linkage_pair F (leftElement F q.1) y
      change F.linkage*pairing F y (leftElement F q.1)=F.left q.1*(y:A) at hpair
      linear_combination
        -weights F q*(y:A)*(F.product q.1 q.2)-weights F q*F.right q.2*hpair
    _=F.linkage*(∑ q, (weights F q*pairing F y (leftElement F q.1))*F.right q.2) :=
      (Finset.mul_sum ..).symm

theorem pairing_injective : Function.Injective (pairing F) := by
  intro y z hyz
  apply Subtype.ext
  rw [right_reconstruction F y,right_reconstruction F z]
  apply Finset.sum_congr rfl
  intro q _
  rw [show pairing F y (leftElement F q.1)=pairing F z (leftElement F q.1) from
    congrArg (fun f : F.leftIdeal →ₗ[A] A => f (leftElement F q.1)) hyz]

def dualInverse (φ : F.leftIdeal →ₗ[A] A) : F.rightIdeal :=
  ∑ q, (weights F q*φ (leftElement F q.1)) • rightElement F q.2

theorem pairing_dualInverse (φ : F.leftIdeal →ₗ[A] A) :
    pairing F (dualInverse F φ)=φ := by
  ext x
  have hx : x=∑ q, (weights F q*pairing F (rightElement F q.2) x) • leftElement F q.1 := by
    apply Subtype.ext
    simpa only [Submodule.coe_sum,Submodule.coe_smul,smul_eq_mul,leftElement] using
      left_reconstruction F x
  have hφ := congrArg φ hx
  simp only [map_sum,map_smul,smul_eq_mul] at hφ
  rw [dualInverse,map_sum,LinearMap.sum_apply]
  calc
    _=∑ q, (weights F q*φ (leftElement F q.1))*pairing F (rightElement F q.2) x := by
      apply Finset.sum_congr rfl
      intro q _
      rw [map_smul,LinearMap.smul_apply,smul_eq_mul]
    _=φ x := by
      rw [hφ]
      apply Finset.sum_congr rfl
      intro q _
      ring

def rightEquivLeftDual : F.rightIdeal ≃ₗ[A] (F.leftIdeal →ₗ[A] A) :=
  LinearEquiv.ofBijective (pairing F)
    ⟨pairing_injective F,fun φ => ⟨dualInverse F φ,pairing_dualInverse F φ⟩⟩

end CycleQ2SegreLinkageDuality

#print axioms CycleQ2SegreLinkageDuality.pairing_selected
#print axioms CycleQ2SegreLinkageDuality.rightEquivLeftDual
end
end

/- Component: continuation_3/CurveQuotientGrading.lean -/
section
/-! # The actual polynomial grading in the six curve coordinates -/

noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2CurveQuotientGrading

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2CurveRestriction
  CycleQ2CurveQuotientFiniteFree CycleQ2CurveCechTwoOpen CycleQ2CurveCechLocalization
  CycleQ2CurveCechLocalizedBasis CycleQ2CurveCechRestrictions

variable (R : Type*) [CommRing R]

def mergeExponent (e d : Fin 2 →₀ ℕ) : CurveExponent :=
  Finsupp.equivFunOnFinite.symm ![e 0,d 0,e 1,d 1]

lemma regroup_coeff_coeff (p : CurvePoly R) (e d : Fin 2 →₀ ℕ) :
    ((regroup R p).coeff e).coeff d=p.coeff (mergeExponent e d) := by
  change ((AddMonoidAlgebra.curryAlgEquiv R
    (AddMonoidAlgebra.domCongr R R Finsupp.sumFinsuppAddEquivProdFinsupp
      (renameEquiv R splitIndex p))).coeff e).coeff d=_
  change (AddMonoidAlgebra.domCongr R R Finsupp.sumFinsuppAddEquivProdFinsupp
    (renameEquiv R splitIndex p)).coeff (e,d)=_
  rw [AddMonoidAlgebra.coeff_domCongr]
  have he : Finsupp.sumFinsuppAddEquivProdFinsupp.symm (e,d)=
      (mergeExponent e d).mapDomain splitIndex := by
    ext z
    obtain ⟨j,rfl⟩ := splitIndex.surjective z
    rw [Finsupp.mapDomain_apply splitIndex.injective]
    fin_cases j <;> rfl
  rw [he]
  exact coeff_rename_mapDomain splitIndex splitIndex.injective p (mergeExponent e d)

def outerExponent {s : Side} (ab : ShiftIndex s) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 ab.1.val+Finsupp.single 1 ab.2.val

lemma regroup_reduced [Nontrivial R] (s : Side) (r ι : R) {p : CurvePoly R}
    (hp : Standard s p) : Reduced nestedOrder (nestedQ R s r) (nestedH R s r ι) (regroup R p) := by
  intro e he
  obtain ⟨d,hd⟩ := exists_coeff_ne_zero (MvPolynomial.mem_support_iff.mp he)
  rw [regroup_coeff_coeff] at hd
  have hb := hp (mergeExponent e d) (MvPolynomial.mem_support_iff.mpr hd)
  apply (reduced_iff R s r ι e).mpr
  exact ⟨hb.1,hb.2⟩

lemma nestedBasis_repr_reduced [Nontrivial R] (s : Side) (r ι : R) (p : Nested R)
    (hp : Reduced nestedOrder (nestedQ R s r) (nestedH R s r ι) p) (ab : ShiftIndex s) :
    (nestedBasis R s r ι).repr (Ideal.Quotient.mk (nestedIdeal R s r ι) p) ab=
      p.coeff (outerExponent ab) := by
  unfold nestedBasis
  erw [Module.Basis.repr_reindex_apply,
    CycleQ2SeedQuotientGrading.quotientBasis_repr_reduced nestedOrder
      (nestedQ R s r) (nestedH R s r ι) p (nestedQ_leading R s r).2
      (nestedH_leading R s r ι).2 (nested_coprime R s r ι) hp]
  rfl

lemma curveBasis_repr_standard [Nontrivial R] (s : Side) (r ι : R) (p : CurvePoly R)
    (hp : Standard s p) (ab : ShiftIndex s) :
    (curveBasis R s r ι).repr (Ideal.Quotient.mk (curveIdeal s r ι) p) ab=
      (regroup R p).coeff (outerExponent ab) := by
  change (nestedBasis R s r ι).repr
    (Ideal.Quotient.mk (nestedIdeal R s r ι) (regroup R p)) ab=_
  exact nestedBasis_repr_reduced R s r ι (regroup R p) (regroup_reduced R s r ι hp) ab

lemma curveBasis_repr_standard_coeff [Nontrivial R] (s : Side) (r ι : R) (p : CurvePoly R)
    (hp : Standard s p) (ab : ShiftIndex s) (d : Fin 2 →₀ ℕ) :
    ((curveBasis R s r ι).repr (Ideal.Quotient.mk (curveIdeal s r ι) p) ab).coeff d=
      p.coeff (mergeExponent (outerExponent ab) d) := by
  rw [curveBasis_repr_standard R s r ι p hp,regroup_coeff_coeff]

def ordinaryDegree (e : CurveExponent) : ℕ := Finsupp.weight (fun _ : Fin 4 => 1) e

theorem ordinaryDegree_eq (e : CurveExponent) : ordinaryDegree e=e 0+e 1+e 2+e 3 := by
  simp [ordinaryDegree,Finsupp.weight, Finsupp.linearCombination_apply,
    Finsupp.sum_fintype,Fin.sum_univ_succ,add_assoc]

theorem mergeExponent_degree {s : Side} (ab : ShiftIndex s) (d : Fin 2 →₀ ℕ) :
    (ordinaryDegree (mergeExponent (outerExponent ab) d):ℤ)=shiftedDegree ab (castExponent d) := by
  rw [ordinaryDegree_eq]
  simp [mergeExponent,outerExponent,shiftedDegree,castExponent]
  ring

@[simp] theorem baseToLaurent_coeff_cast (p : Base R) (d : Fin 2 →₀ ℕ) :
    (baseToLaurent R p).coeff (castExponent d)=p.coeff d :=
  Finsupp.mapDomain_apply castExponent_injective _ _

def SignedHomogeneous (p : CurvePoly R) (d : ℤ) : Prop :=
  ∀ e, p.coeff e≠0 → (ordinaryDegree e:ℤ)=d

theorem signedHomogeneous_iff (p : CurvePoly R) (d : ℕ) :
    SignedHomogeneous R p (d:ℤ) ↔ p.IsWeightedHomogeneous (fun _ : Fin 4 => 1) d := by
  constructor
  · intro hp e he
    exact Nat.cast_injective (hp e he)
  · intro hp e he
    exact congrArg (fun n : ℕ => (n:ℤ)) (hp he)

lemma standard_coordinates_homogeneous [Nontrivial R] (s : Side) (r ι : R)
    (p : CurvePoly R) (d : ℤ) (hs : Standard s p) (hp : SignedHomogeneous R p d)
    (ab : ShiftIndex s) :
    HasDegree ab d (baseToLaurent R ((curveBasis R s r ι).repr
      (Ideal.Quotient.mk (curveIdeal s r ι) p) ab)) := by
  intro e he
  by_contra hne
  have hpos : ∀ i,0≤e i := by
    intro i
    by_contra hi
    exact hne (baseToLaurent_hasPoles R _ e i (by simp) (lt_of_not_ge hi))
  obtain ⟨a,rfl⟩ := (mem_range_castExponent e).mpr hpos
  rw [baseToLaurent_coeff_cast,curveBasis_repr_standard_coeff R s r ι p hs] at hne
  have hh := hp _ hne
  rw [mergeExponent_degree] at hh
  exact he hh

theorem quotient_normal [Nontrivial R] (s : Side) (r ι : R) (p : CurvePoly R) :
    Ideal.Quotient.mk (curveIdeal s r ι) p=
      Ideal.Quotient.mk (curveIdeal s r ι) (normal s r ι p) := by
  obtain ⟨_,a,b,hab⟩ := normal_spec s r ι p
  apply Ideal.Quotient.eq.mpr
  apply Ideal.mem_span_pair.mpr
  refine ⟨a,b,?_⟩
  exact (sub_eq_iff_eq_add.mpr hab).symm

theorem coordinates_homogeneous [Nontrivial R] (s : Side) (r ι : R)
    (p : CurvePoly R) (d : ℕ) (hp : p.IsWeightedHomogeneous (fun _ : Fin 4 => 1) d)
    (ab : ShiftIndex s) :
    HasDegree ab (d:ℤ) (baseToLaurent R ((curveBasis R s r ι).repr
      (Ideal.Quotient.mk (curveIdeal s r ι) p) ab)) := by
  rw [quotient_normal]
  exact standard_coordinates_homogeneous R s r ι (normal s r ι p) d
    (normal_spec s r ι p).1 ((signedHomogeneous_iff R _ d).mpr (normal_homogeneous s r ι hp)) ab

theorem coordinates_signedHomogeneous [Nontrivial R] (s : Side) (r ι : R)
    (p : CurvePoly R) (d : ℤ) (hp : SignedHomogeneous R p d) (ab : ShiftIndex s) :
    HasDegree ab d (baseToLaurent R ((curveBasis R s r ι).repr
      (Ideal.Quotient.mk (curveIdeal s r ι) p) ab)) := by
  by_cases hz : p=0
  · subst p
    intro e he
    simp
  · obtain ⟨e,he⟩ := exists_coeff_ne_zero hz
    have hd := hp e he
    have hh : p.IsWeightedHomogeneous (fun _ : Fin 4 => 1) (ordinaryDegree e) :=
      (signedHomogeneous_iff R p _).mp (hd.symm ▸ hp)
    exact hd ▸ coordinates_homogeneous R s r ι p _ hh ab

theorem standard_signedHomogeneous_iff_coordinates [Nontrivial R] (s : Side) (r ι : R)
    (p : CurvePoly R) (d : ℤ) (hs : Standard s p) :
    SignedHomogeneous R p d ↔ ∀ ab, HasDegree ab d
      (baseToLaurent R ((curveBasis R s r ι).repr (Ideal.Quotient.mk (curveIdeal s r ι) p) ab)) := by
  constructor
  · intro hp ab
    exact standard_coordinates_homogeneous R s r ι p d hs hp ab
  · intro hc e he
    have hb := hs e (MvPolynomial.mem_support_iff.mpr he)
    let ab : ShiftIndex s := (⟨e 0,hb.1⟩,⟨e 2,hb.2⟩)
    let a : Fin 2 →₀ ℕ := Finsupp.equivFunOnFinite.symm ![e 1,e 3]
    have heq : mergeExponent (outerExponent ab) a=e := by
      ext i
      fin_cases i <;> simp [mergeExponent,outerExponent,ab,a]
    rw [← heq,mergeExponent_degree]
    by_contra hg
    have hz := hc ab (castExponent a) hg
    rw [baseToLaurent_coeff_cast,curveBasis_repr_standard_coeff R s r ι p hs] at hz
    exact he (heq ▸ hz)

theorem exists_signed_homogeneous_representative [Nontrivial R] (s : Side) (r ι : R)
    (q : CurveRing s r ι) (d : ℤ)
    (hq : ∀ ab,HasDegree ab d (baseToLaurent R ((curveBasis R s r ι).repr q ab))) :
    ∃ p : CurvePoly R, Standard s p ∧ SignedHomogeneous R p d ∧
      Ideal.Quotient.mk (curveIdeal s r ι) p=q := by
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective q
  refine ⟨normal s r ι p,(normal_spec s r ι p).1,?_,(quotient_normal R s r ι p).symm⟩
  apply (standard_signedHomogeneous_iff_coordinates R s r ι _ d (normal_spec s r ι p).1).mpr
  rw [← quotient_normal]
  exact hq

def baseDegree : LaurentExponent →+ ℤ where
  toFun e := e 0+e 1
  map_zero' := by simp
  map_add' e f := by simp; ring

theorem shiftedDegree_add {side : Side} (ab : ShiftIndex side) (e f : LaurentExponent) :
    shiftedDegree ab (e+f)=shiftedDegree ab e+baseDegree f := by
  simp [shiftedDegree,baseDegree]
  ring

theorem hasDegree_mul_T {side : Side} (ab : ShiftIndex side) (d : ℤ) (e : LaurentExponent)
    (p : Laurent (R:=R)) (hp : HasDegree ab d p) :
    HasDegree ab (d+baseDegree e) (p*T R e) := by
  intro f hf
  rw [coeff_mul_T]
  apply hp
  intro hh
  apply hf
  calc
    shiftedDegree ab f=shiftedDegree ab ((f-e)+e) := by rw [sub_add_cancel]
    _ =shiftedDegree ab (f-e)+baseDegree e := shiftedDegree_add ab _ _
    _ =d+baseDegree e := by rw [hh]

theorem coordinates_fraction [Nontrivial R] (side : Side) (r ι : R) (s : Finset (Fin 2))
    (q : CurveLocal R side r ι s) (num : CurveRing side r ι) (n : ℕ)
    (h : q * algebraMap (CurveRing side r ι) (CurveLocal R side r ι s)
      (algebraMap (Base R) (CurveRing side r ι) (baseProduct R s ^ n)) =
      algebraMap (CurveRing side r ι) (CurveLocal R side r ι s) num) (ab : (ShiftIndex side)) :
    baseToLaurent R ((curveBasis R side r ι).repr num ab) =
      localizedCoordinates R side r ι s q ab * T R (n • openExponent s) := by
  have hh := congrArg (fun z ↦ localizedCoordinates R side r ι s z ab) h
  rw [coordinates_mul_base, localizedCoordinates_algebraMap] at hh
  simp only [map_pow, baseToLaurent_baseProduct, T_pow] at hh
  exact hh.symm.trans (mul_comm _ _)

/-- The coordinate definition of a graded local section agrees with an
actual fraction having a polynomial numerator of the required original grade. -/
theorem localized_homogeneous_iff_fraction [Nontrivial R] (side : Side) (r ι : R)
    (s : Finset (Fin 2)) (q : CurveLocal R side r ι s) (g : ℤ) :
    (∀ ab, HasDegree ab g (localizedCoordinates R side r ι s q ab)) ↔
      ∃ (n : ℕ) (p : CurvePoly R),
        SignedHomogeneous R p (g + baseDegree (n • openExponent s)) ∧
        q * algebraMap (CurveRing side r ι) (CurveLocal R side r ι s)
          (algebraMap (Base R) (CurveRing side r ι) (baseProduct R s ^ n)) =
          algebraMap (CurveRing side r ι) (CurveLocal R side r ι s)
            (Ideal.Quotient.mk (curveIdeal side r ι) p) := by
  constructor
  · intro hq
    obtain ⟨n, num, hn⟩ := IsLocalization.Away.surj
      (algebraMap (Base R) (CurveRing side r ι) (baseProduct R s)) q
    have hn' : q * algebraMap (CurveRing side r ι) (CurveLocal R side r ι s)
        (algebraMap (Base R) (CurveRing side r ι) (baseProduct R s ^ n)) =
        algebraMap (CurveRing side r ι) (CurveLocal R side r ι s) num := by
      simpa only [map_pow] using hn
    have hnum (ab : (ShiftIndex side)) :
        HasDegree ab (g + baseDegree (n • openExponent s))
          (baseToLaurent R ((curveBasis R side r ι).repr num ab)) := by
      rw [coordinates_fraction R side r ι s q num n hn' ab]
      exact hasDegree_mul_T R ab g _ _ (hq ab)
    obtain ⟨p, _, hp, hpn⟩ := exists_signed_homogeneous_representative R side r ι num _ hnum
    refine ⟨n, p, hp, ?_⟩
    simpa only [hpn] using hn'
  · rintro ⟨n, p, hp, hfrac⟩ ab
    have hh := coordinates_fraction R side r ι s q
      (Ideal.Quotient.mk (curveIdeal side r ι) p) n hfrac ab
    have hnum := coordinates_signedHomogeneous R side r ι p _ hp ab
    have hrep : localizedCoordinates R side r ι s q ab =
        baseToLaurent R ((curveBasis R side r ι).repr
          (Ideal.Quotient.mk (curveIdeal side r ι) p) ab) *
          T R (-(n • openExponent s)) := by
      have hm := congrArg (fun z ↦ z * T R (-(n • openExponent s))) hh
      simpa only [mul_assoc, T_mul, add_neg_cancel, T_zero, mul_one] using hm.symm
    rw [hrep]
    have hz := hasDegree_mul_T R ab _ (-(n • openExponent s)) _ hnum
    simpa only [map_neg, add_neg_cancel_right] using hz


end CycleQ2CurveQuotientGrading

#print axioms CycleQ2CurveQuotientGrading.coordinates_homogeneous
#print axioms CycleQ2CurveQuotientGrading.exists_signed_homogeneous_representative

#print axioms CycleQ2CurveQuotientGrading.localized_homogeneous_iff_fraction
end
end

/- Component: continuation_3/LinkageComponentAlgebra.lean -/
section
/-! Coefficient maps, the second linkage ideal, and an actual complex cube
root for the elementary component decomposition. -/

noncomputable section
set_option maxHeartbeats 500000
set_option maxRecDepth 20000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2LinkageComponentAlgebra

open CycleQ2SegreSeed CycleQ2LinkageComponentDecomposition
variable {R S : Type*} [CommRing R] [CommRing S]

theorem map_linkageE (φ : R →+* S) (a b c d : R) (j : Fin 5) :
    φ (linkageE a b c d j)=linkageE (φ a) (φ b) (φ c) (φ d) j := by
  fin_cases j <;> simp [linkageE,linkageP]

theorem map_linkageEprime (φ : R →+* S) (a b c d : R) (j : Fin 5) :
    φ (linkageEprime a b c d j)=linkageEprime (φ a) (φ b) (φ c) (φ d) j := by
  fin_cases j <;> simp [linkageEprime,linkageP]

theorem map_leftIdeal (φ : R →+* S) (a b c d : R) :
    (leftIdeal a b c d).map φ=leftIdeal (φ a) (φ b) (φ c) (φ d) := by
  simp only [leftIdeal,Ideal.map_span,← Set.range_comp]
  congr 1
  apply congrArg Set.range
  funext j
  exact map_linkageE φ a b c d j

theorem right_generator_transformed (a b c d : R) (j : Fin 5) :
    linkageE a (-d) c (-b) j=if j=2 then -linkageEprime a b c d j else linkageEprime a b c d j := by
  fin_cases j <;> simp [linkageE,linkageEprime,linkageP] <;> ring

theorem rightIdeal_eq_leftIdeal (a b c d : R) :
    Ideal.span (Set.range (linkageEprime a b c d))=leftIdeal a (-d) c (-b) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro x ⟨j,rfl⟩
    have h := leftGenerator_mem a (-d) c (-b) j
    rw [right_generator_transformed] at h
    split_ifs at h with hj
    · exact (leftIdeal a (-d) c (-b)).neg_mem_iff.mp h
    · exact h
  · apply Ideal.span_le.mpr
    rintro x ⟨j,rfl⟩
    rw [right_generator_transformed]
    have h : linkageEprime a b c d j∈Ideal.span (Set.range (linkageEprime a b c d)) :=
      Ideal.subset_span ⟨j,rfl⟩
    split_ifs
    · exact (Ideal.span (Set.range (linkageEprime a b c d))).neg_mem h
    · exact h

theorem map_componentIdeal (φ : R →+* S) (z a b c d : R) :
    (componentIdeal z a b c d).map φ=componentIdeal (φ z) (φ a) (φ b) (φ c) (φ d) := by
  simp only [componentIdeal,Ideal.map_span,← Set.range_comp]
  congr 1
  apply congrArg Set.range
  funext j
  fin_cases j <;> simp [componentGenerator]

theorem rootValues_eq_pow (z : R) (i : Fin 3) : rootValues z i=z^i.val := by
  fin_cases i <;> simp [rootValues]

def complexRoot : ℂ := Complex.exp (2*(Real.pi:ℂ)*Complex.I/3)

theorem complexRoot_primitive : IsPrimitiveRoot complexRoot 3 :=
  Complex.isPrimitiveRoot_exp 3 (by decide)

theorem complexRoot_quadratic : complexRoot^2+complexRoot+1=0 := by
  have h := complexRoot_primitive.geom_sum_eq_zero (by decide : 1<3)
  norm_num [Finset.sum_range_succ] at h
  linear_combination h

theorem complexRoot_cube : complexRoot^3=1 := complexRoot_primitive.pow_eq_one

theorem complexRoot_units (i j : Fin 3) (hij : i≠j) :
    IsUnit (rootValues complexRoot i-rootValues complexRoot j) ∧
      IsUnit (rootValues complexRoot i^2-rootValues complexRoot j^2) := by
  constructor
  · apply isUnit_iff_ne_zero.mpr
    intro h
    apply hij
    apply Fin.ext
    apply complexRoot_primitive.pow_inj i.isLt j.isLt
    simpa only [rootValues_eq_pow] using sub_eq_zero.mp h
  · apply isUnit_iff_ne_zero.mpr
    intro h
    apply hij
    apply Fin.ext
    apply (complexRoot_primitive.pow_of_coprime 2 (by decide)).pow_inj i.isLt j.isLt
    have he := sub_eq_zero.mp h
    simp only [rootValues_eq_pow] at he
    calc
      (complexRoot^2)^i.val=(complexRoot^i.val)^2 := by rw [←pow_mul,←pow_mul,Nat.mul_comm]
      _=(complexRoot^j.val)^2 := he
      _=(complexRoot^2)^j.val := by rw [←pow_mul,←pow_mul,Nat.mul_comm]

theorem mapped_rootValues (φ : ℂ →+* R) (i : Fin 3) :
    φ (rootValues complexRoot i)=rootValues (φ complexRoot) i := by
  fin_cases i <;> simp [rootValues]

theorem mapped_root_units (φ : ℂ →+* R) (i j : Fin 3) (hij : i≠j) :
    IsUnit (rootValues (φ complexRoot) i-rootValues (φ complexRoot) j) ∧
      IsUnit (rootValues (φ complexRoot) i^2-rootValues (φ complexRoot) j^2) := by
  have h := complexRoot_units i j hij
  constructor
  · simpa only [map_sub,mapped_rootValues] using h.1.map φ
  · simpa only [map_sub,map_pow,mapped_rootValues] using h.2.map φ

end CycleQ2LinkageComponentAlgebra

#print axioms CycleQ2LinkageComponentAlgebra.rightIdeal_eq_leftIdeal
#print axioms CycleQ2LinkageComponentAlgebra.complexRoot_units
end
end

/- Component: continuation_3/cylinder_bridge/ModularFactorChartExact.lean -/
section
/-! # Factor exactness on the actual modular coordinate charts

Every hypothesis of the factor sequence is discharged for the literal
smooth incidence seed at r=57 and i=33 over F109. The two modules are the
actual localized linkage ideals.
-/

noncomputable section
set_option maxHeartbeats 300000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2ModularFactorChartExact

open CycleQ2IncidenceGaussianArithmetic

open Matrix CycleQ2IncidenceFirstOrder CycleQ2SegreTangentLocal
  CycleQ2SeedQuotientFiniteFree CycleQ2SeedCechLocalization
  CycleQ2SeedCechLocalizedBasis CycleQ2SeedLinkageIdeals
  CycleQ2SegreFactorSequence

abbrev Chart (s : Finset (Fin 3)) := SeedLocal F109 57 33 s

def chartMap (s : Finset (Fin 3)) : SeedRing (57:F109) 33 →+* Chart s :=
  algebraMap (SeedRing (57:F109) 33) (Chart s)

def leftIdeal (s : Finset (Fin 3)) : Ideal (Chart s) :=
  (linkageIdeal .left (57:F109) 33).map (chartMap s)

def rightIdeal (s : Finset (Fin 3)) : Ideal (Chart s) :=
  (linkageIdeal .right (57:F109) 33).map (chartMap s)

def leftSection (s : Finset (Fin 3)) (i : Fin 3) : Chart s :=
  chartMap s (CycleQ2SeedLinkagePrincipal.leftSection (57:F109) 33 i)

def rightSection (s : Finset (Fin 3)) (j : Fin 3) : Chart s :=
  chartMap s (CycleQ2SeedLinkagePrincipal.rightSection (57:F109) 33 j)

def linkage (s : Finset (Fin 3)) : Chart s :=
  chartMap s (CycleQ2SeedLinkagePrincipal.linkage (57:F109) 33)

theorem linkage_regular (s : Finset (Fin 3)) :
    Function.Injective (fun z : Chart s => linkage s*z) := by
  apply CycleQ2LinkageIdealPrincipal.localization_mul_injective
    (Algebra.algebraMapSubmonoid (SeedRing (57:F109) 33)
      (Submonoid.powers (baseProduct F109 s))) (Chart s)
    (CycleQ2SeedLinkagePrincipal.linkage (57:F109) 33)
  apply CycleQ2SeedLinkageRegular.linkage_mul_injective
  exact (by decide : (33:F109)≠1)

theorem chart_ideals_pairing (s : Finset (Fin 3)) :
    leftIdeal s*rightIdeal s≤Ideal.span {linkage s} := by
  dsimp only [leftIdeal,rightIdeal,linkage]
  exact @CycleQ2SeedLinkagePrincipal.mapped_ideals_pairing F109 inferInstance
    (Chart s) inferInstance (57:F109) 33 (chartMap s)

def factorData (s : Finset (Fin 3)) (hs : s.Nonempty) : FactorData (Chart s) where
  leftIdeal := leftIdeal s
  rightIdeal := rightIdeal s
  linkage := linkage s
  matrix := CycleQ2SegreModularChartExact.chartMatrix (R:=F109) s
  left := leftSection s
  right := rightSection s
  left_mem i := Ideal.mem_map_of_mem (chartMap s)
    (CycleQ2SeedLinkagePrincipal.leftSection_mem (57:F109) 33 i)
  right_mem j := Ideal.mem_map_of_mem (chartMap s)
    (CycleQ2SeedLinkagePrincipal.rightSection_mem (57:F109) 33 j)
  product i j := by
    have h := congrArg (chartMap s)
      (CycleQ2SeedLinkagePrincipal.selected_product (57:F109) 33 i j)
    simpa only [map_mul,leftSection,rightSection,linkage,
      CycleQ2SegreModularChartExact.chartMatrix,CycleQ2SegreModularBasepoint.matrix,
      RingHom.mapMatrix_apply,Matrix.map_apply,chartMap] using h
  ideals_product := chart_ideals_pairing s
  regular := linkage_regular s
  cofactors_zero := CycleQ2SegreModularChartExact.chartMatrix_cofactors (R:=F109) s
  entries_generate := CycleQ2SegreModularChartExact.chartMatrix_entries_generate (R:=F109) s hs

abbrev FactorSections (s : Finset (Fin 3)) :=
  (Fin 3 → leftIdeal s) × (Fin 3 → rightIdeal s)

def chartFactorMap (s : Finset (Fin 3)) (hs : s.Nonempty) :
    FactorSections s →ₗ[Chart s] Matrix (Fin 3) (Fin 3) (Chart s) :=
  factorMap (factorData s hs)

def chartGaugeMap (s : Finset (Fin 3)) (hs : s.Nonempty) :
    Chart s →ₗ[Chart s] FactorSections s := gaugeMap (factorData s hs)

theorem chartFactorMap_formula (s : Finset (Fin 3)) (hs : s.Nonempty)
    (v : FactorSections s) (i j : Fin 3) :
    linkage s*chartFactorMap s hs v i j=
      (v.1 i:Chart s)*rightSection s j+leftSection s i*(v.2 j:Chart s) :=
  linkage_factorMap (factorData s hs) v i j

/-- The literal local short exact factor sequence, without a rank,
local-pivot, ideal-pairing or regularity hypothesis. -/
theorem actual_factor_sequence (s : Finset (Fin 3)) (hs : s.Nonempty) :
    Function.Injective (chartGaugeMap s hs) ∧
    LinearMap.ker (chartFactorMap s hs)=LinearMap.range (chartGaugeMap s hs) ∧
    LinearMap.range (chartFactorMap s hs)=
      LinearMap.ker (cofactorDifferentialLinear (CycleQ2SegreModularChartExact.chartMatrix (R:=F109) s)) :=
  ⟨gaugeMap_injective (factorData s hs),
    ker_factorMap_eq_range_gaugeMap (factorData s hs),
    range_factorMap_eq_ker_differential (factorData s hs)⟩

end CycleQ2ModularFactorChartExact

#print axioms CycleQ2ModularFactorChartExact.linkage_regular
#print axioms CycleQ2ModularFactorChartExact.actual_factor_sequence
end
end

/- Component: continuation_3/ModularGlobalFactorSpaces.lean -/
section
/-! The actual finite-field source and global factor ambient spaces. The
factor ambient spaces are the literal curve restriction kernels; no equality
with the global linkage ideal pieces is needed for the dimension argument. -/

noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CycleQ2ModularGlobalFactorSpaces

open Matrix MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2IncidenceFirstOrder CycleQ2IncidenceGradedBasis CycleQ2SegreTangentLocal
  CycleQ2CurveRestriction CycleQ2CurveRestrictionModularData
  CycleQ2CurveRestrictionModularChecks CycleQ2SeedLinkageIdeals

abbrev K := CycleQ2IncidenceGaussianArithmetic.F109
abbrev A := SeedRing (57:K) 33
abbrev Input14 := Matrix (Fin 3) (Fin 3) (SeedPiece (57:K) 33 14 0)
abbrev LeftPiece := LinearMap.ker (seedRestrictionPiece .left (57:K) 33 10 0)
abbrev RightPiece := LinearMap.ker (seedRestrictionPiece .right (57:K) 33 8 1)
abbrev Domain := (Fin 3 → LeftPiece) × (Fin 3 → RightPiece)

instance leftPiece_finite : Module.Finite K LeftPiece := by
  letI : Module.Finite K (SeedPiece (57:K) 33 10 0) :=
    Module.Finite.of_basis (seedPieceBasis (57:K) 33 10 0 (by decide))
  exact Module.Finite.of_injective (LinearMap.ker (seedRestrictionPiece .left (57:K) 33 10 0)).subtype
    Subtype.val_injective

instance rightPiece_finite : Module.Finite K RightPiece := by
  letI : Module.Finite K (SeedPiece (57:K) 33 8 1) :=
    Module.Finite.of_basis (seedPieceBasis (57:K) 33 8 1 (by decide))
  exact Module.Finite.of_injective (LinearMap.ker (seedRestrictionPiece .right (57:K) 33 8 1)).subtype
    Subtype.val_injective

instance input14_finite : Module.Finite K Input14 := by
  letI : Module.Finite K (SeedPiece (57:K) 33 14 0) :=
    Module.Finite.of_basis (seedPieceBasis (57:K) 33 14 0 (by decide))
  exact Module.Finite.pi (R:=K) (M:=fun _ : Fin 3 => Fin 3 → SeedPiece (57:K) 33 14 0)

instance domain_finite : Module.Finite K Domain := by
  letI : Module.Finite K (Fin 3 → LeftPiece) := Module.Finite.pi (R:=K) (M:=fun _ : Fin 3 => LeftPiece)
  letI : Module.Finite K (Fin 3 → RightPiece) := Module.Finite.pi (R:=K) (M:=fun _ : Fin 3 => RightPiece)
  exact Module.Finite.prod

theorem left_restriction_surjective :
    Function.Surjective (seedRestrictionPiece .left (57:K) 33 10 0) :=
  seedRestrictionPiece_surjective_of_minor .left 57 33 10 0 57
    leftRows leftSources left_rows_cover left_sources_good (left_minor_det_ne_zero (R:=K))

theorem right_restriction_surjective :
    Function.Surjective (seedRestrictionPiece .right (57:K) 33 8 1) :=
  seedRestrictionPiece_surjective_of_minor .right 57 33 8 1 45
    rightRows rightSources right_rows_cover right_sources_good (right_minor_det_ne_zero (R:=K))

theorem leftPiece_finrank : Module.finrank K LeftPiece=56 := by
  letI : Module.Finite K (SeedPiece (57:K) 33 10 0) :=
    Module.Finite.of_basis (seedPieceBasis (57:K) 33 10 0 (by decide))
  have h := (seedRestrictionPiece .left (57:K) 33 10 0).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr left_restriction_surjective,finrank_top,
    left_seedPiece_rank,left_curvePiece_rank] at h
  change 57+Module.finrank K LeftPiece=113 at h
  omega

theorem rightPiece_finrank : Module.finrank K RightPiece=23 := by
  letI : Module.Finite K (SeedPiece (57:K) 33 8 1) :=
    Module.Finite.of_basis (seedPieceBasis (57:K) 33 8 1 (by decide))
  have h := (seedRestrictionPiece .right (57:K) 33 8 1).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr right_restriction_surjective,finrank_top,
    right_seedPiece_rank,right_curvePiece_rank] at h
  change 45+Module.finrank K RightPiece=68 at h
  omega

theorem domain_finrank : Module.finrank K Domain=237 := by
  letI : Module.Free K LeftPiece := Module.Free.of_divisionRing K LeftPiece
  letI : Module.Free K RightPiece := Module.Free.of_divisionRing K RightPiece
  letI : Module.Finite K (Fin 3 → LeftPiece) := Module.Finite.pi (R:=K) (M:=fun _ : Fin 3 => LeftPiece)
  letI : Module.Finite K (Fin 3 → RightPiece) := Module.Finite.pi (R:=K) (M:=fun _ : Fin 3 => RightPiece)
  letI : Module.Free K (Fin 3 → LeftPiece) := Module.Free.of_divisionRing K (Fin 3 → LeftPiece)
  letI : Module.Free K (Fin 3 → RightPiece) := Module.Free.of_divisionRing K (Fin 3 → RightPiece)
  change Module.finrank K ((Fin 3 → LeftPiece) × (Fin 3 → RightPiece))=237
  rw [Module.finrank_prod]
  simp only [Module.finrank_pi_fintype,leftPiece_finrank,rightPiece_finrank,
    Finset.sum_const,Fintype.card_fin,Finset.card_univ,smul_eq_mul]

theorem degree14Piece_finrank : Module.finrank K (SeedPiece (57:K) 33 14 0)=239 := by
  change Module.finrank K (quotientPiece fullGrading (smoothH (33:K)) (smoothF (57:K) 33) (14,0))=239
  rw [seed_h_normalized,seed_F_normalized]
  exact fullPiece_degree14_finrank _ _

theorem input14_finrank : Module.finrank K Input14=2151 := by
  letI : Module.Finite K (SeedPiece (57:K) 33 14 0) :=
    Module.Finite.of_basis (seedPieceBasis (57:K) 33 14 0 (by decide))
  letI : Module.Finite K (Fin 3 → SeedPiece (57:K) 33 14 0) :=
    Module.Finite.pi (R:=K) (M:=fun _ : Fin 3 => SeedPiece (57:K) 33 14 0)
  letI : Module.Free K (SeedPiece (57:K) 33 14 0) :=
    Module.Free.of_divisionRing K (SeedPiece (57:K) 33 14 0)
  letI : Module.Free K (Fin 3 → SeedPiece (57:K) 33 14 0) :=
    Module.Free.of_divisionRing K (Fin 3 → SeedPiece (57:K) 33 14 0)
  change Module.finrank K (Fin 3 → Fin 3 → SeedPiece (57:K) 33 14 0)=2151
  simp only [Module.finrank_pi_fintype,degree14Piece_finrank,Finset.sum_const,Fintype.card_fin,
    Finset.card_univ,smul_eq_mul]

def inputToGlobal : Input14 →ₗ[K] Matrix (Fin 3) (Fin 3) A where
  toFun N i j := (N i j).val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem inputToGlobal_injective : Function.Injective inputToGlobal := by
  intro N P h
  funext i j
  apply Subtype.ext
  exact congrArg (fun M : Matrix (Fin 3) (Fin 3) A => M i j) h

def entryDifferential : Input14 →ₗ[K] Matrix (Fin 3) (Fin 3) A :=
  ((cofactorDifferentialLinear (seedQuotientMatrix (57:K) 33)).restrictScalars K).comp inputToGlobal

def leftValue (v : Domain) (i : Fin 3) : A := (v.1 i).val.val
def rightValue (v : Domain) (j : Fin 3) : A := (v.2 j).val.val
def left (i : Fin 3) : A := CycleQ2SeedLinkagePrincipal.leftSection (57:K) 33 i
def right (j : Fin 3) : A := CycleQ2SeedLinkagePrincipal.rightSection (57:K) 33 j
def linkage : A := CycleQ2SeedLinkagePrincipal.linkage (57:K) 33

theorem linkage_regular : Function.Injective (fun z : A => linkage*z) :=
  CycleQ2SeedLinkageRegular.linkage_mul_injective (57:K) 33 (by decide)

def leftClass (i : Fin 3) : LeftPiece :=
  ⟨⟨left i,Submodule.mem_map.mpr ⟨CycleQ2SeedFactorHomogeneous.polynomialLeft (57:K) i,
    CycleQ2SeedFactorHomogeneous.polynomialLeft_homogeneous (57:K) i,rfl⟩⟩,by
    apply Subtype.ext
    exact linkageIdeal_le_restrictionKernel .left (57:K) 33
      (CycleQ2SeedLinkagePrincipal.leftSection_mem (57:K) 33 i)⟩

def rightClass (j : Fin 3) : RightPiece :=
  ⟨⟨right j,Submodule.mem_map.mpr ⟨CycleQ2SeedFactorHomogeneous.polynomialRight (57:K) j,
    CycleQ2SeedFactorHomogeneous.polynomialRight_homogeneous (57:K) j,rfl⟩⟩,by
    apply Subtype.ext
    exact linkageIdeal_le_restrictionKernel .right (57:K) 33
      (CycleQ2SeedLinkagePrincipal.rightSection_mem (57:K) 33 j)⟩

def gaugeVector : Domain := (leftClass,fun j => -rightClass j)

end CycleQ2ModularGlobalFactorSpaces

#print axioms CycleQ2ModularGlobalFactorSpaces.domain_finrank
#print axioms CycleQ2ModularGlobalFactorSpaces.input14_finrank
end
end

/- Component: continuation_3/SeedCyclicAction.lean -/
section
/-! The literal diagonal cubic-root action and its eigenvalue on every
polynomial of the actual degree/character grading. -/

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 10000
set_option maxRecDepth 20000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SeedCyclicAction

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2SegreTangentLocal CycleQ2SeedQuotientGrading

variable {R : Type*} [CommRing R]

theorem polynomialAction_signedHomogeneous (ζ : R) (hζ : ζ^3=1)
    (p : Poly R) (g : CycleQ2SeedCechThreeOpen.LaurentGrade)
    (hp : SignedHomogeneous R p g) : polynomialAction ζ p=C (ζ^g.2.val)*p := by
  by_cases hz : p=0
  · simp [hz]
  · obtain ⟨e,he⟩ := exists_coeff_ne_zero hz
    have hg := hp e he
    have hh : HG p (Finsupp.weight fullGrading e) := by
      apply (signedHomogeneous_iff R p _).mp
      exact hg.symm ▸ hp
    have hact := polynomialAction_homogeneous ζ hζ p
      (Finsupp.weight fullGrading e).1 (Finsupp.weight fullGrading e).2 hh
    have hch : (Finsupp.weight fullGrading e).2=g.2 := congrArg Prod.snd hg
    simpa only [hch] using hact

end CycleQ2SeedCyclicAction

#print axioms CycleQ2SeedCyclicAction.polynomialAction_homogeneous
#print axioms CycleQ2SeedCyclicAction.seedAction
end
end

/- Component: continuation_3/SeedLinkageOrbitCover.lean -/
section
/-! The common vertex of the three explicit linkage components is absent
from every nonempty actual seed coordinate chart. -/

noncomputable section
set_option maxHeartbeats 100000
set_option synthInstance.maxHeartbeats 10000
set_option maxRecDepth 20000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SeedLinkageOrbitCover

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2SegreTangentLocal CycleQ2SeedLinkageIdeals CycleQ2SeedLinkagePrincipal
  CycleQ2CurveRestriction CycleQ2SeedQuotientFiniteFree CycleQ2SeedCechLocalizedBasis
  CycleQ2SeedCechRestrictions CycleQ2SeedCechLocalization

variable {K : Type*} [Field K]

def seedCoordinate (r ι : K) (i : Fin 5) : SeedRing r ι := quotientMap r ι (X i)
def linkageA (r ι : K) : SeedRing r ι := quotientMap r ι (X 0^2)
def linkageB (r ι : K) : SeedRing r ι := quotientMap r ι (C r*X 1*X 3)
def linkageC (r ι : K) : SeedRing r ι := quotientMap r ι (X 4)
def linkageD (r ι : K) : SeedRing r ι := quotientMap r ι (X 2^2)

theorem variables_zero_of_vertex (s : Side) (r ι : K)
    (hr : r≠0) (hι : ι≠0) (hι1 : ι≠1)
    {D : Type*} [CommRing D] [IsDomain D] (f : Poly K →+* D)
    (hb0 : f (C r*X 1*X 3)=0) (hd0 : f (X 2^2)=0)
    (hgen : ∀ j : Fin 5, f (linkageGenerator s r j)=0) (hH : f (smoothH ι)=0) :
    ∀ i : Fin 5, f (X i)=0 := by
  have hconst (c : K) (hc : c≠0) : f (C c)≠0 := by
    exact (map_ne_zero (f.comp C)).mpr hc
  have h2 : f (X 2)=0 := eq_zero_of_pow_eq_zero (by simpa only [map_pow] using hd0)
  have h0pow : f (X 0)^6=0 := by
    have hh := hgen 1
    cases s
    · change f ((X 0^2)^3-(C r*X 1*X 3)^3)=0 at hh
      simpa [map_sub,map_pow,hb0,←pow_mul] using hh
    · change f ((X 0^2)^3+(X 2^2)^3)=0 at hh
      simpa [map_add,map_pow,h2,←pow_mul] using hh
  have h0 : f (X 0)=0 := eq_zero_of_pow_eq_zero h0pow
  have hwpow : f (X 4)^3=0 := by
    have hh := hgen 4
    cases s
    · change f (X 4^3+(X 2^2)^3)=0 at hh
      simpa [map_add,map_pow,h2] using hh
    · change f (-(C r*X 1*X 3)^3+X 4^3)=0 at hh
      simpa [map_add,map_neg,map_pow,hb0] using hh
  have hw : f (X 4)=0 := eq_zero_of_pow_eq_zero hwpow
  have h13 : f (X 1)*f (X 3)=0 := by
    rw [map_mul,map_mul,mul_assoc] at hb0
    exact (mul_eq_zero.mp hb0).resolve_left (hconst r hr)
  have hred : f (C (1-ι))*f (X 3)^3-f (C ι)*f (X 1)^3=0 := by
    simp only [smoothH,smoothB,smoothA,map_sub,map_add,map_mul,map_pow,h0,h2,
      zero_pow (by decide : 3≠0),zero_mul,mul_zero,add_zero,zero_add] at hH
    simp only [map_sub,map_one]
    linear_combination hH
  have h1h3 : f (X 1)=0 ∧ f (X 3)=0 := by
    rcases mul_eq_zero.mp h13 with h1 | h3
    · refine ⟨h1,?_⟩
      rw [h1,zero_pow (by decide : 3≠0),mul_zero,sub_zero] at hred
      exact eq_zero_of_pow_eq_zero ((mul_eq_zero.mp hred).resolve_left (hconst (1-ι) (sub_ne_zero.mpr (Ne.symm hι1))))
    · refine ⟨?_,h3⟩
      rw [h3,zero_pow (by decide : 3≠0),mul_zero,zero_sub,neg_eq_zero] at hred
      exact eq_zero_of_pow_eq_zero ((mul_eq_zero.mp hred).resolve_left (hconst ι hι))
  intro i
  fin_cases i
  · exact h0
  · exact h1h3.1
  · exact h2
  · exact h1h3.2
  · exact hw

theorem seedCoordinates_mem_of_vertex (s : Side) (r ι : K)
    (hr : r≠0) (hι : ι≠0) (hι1 : ι≠1)
    (P : Ideal (SeedRing r ι)) [P.IsPrime]
    (hE : linkageIdeal s r ι≤P) (hb : linkageB r ι∈P) (hd : linkageD r ι∈P) :
    ∀ i : Fin 5, seedCoordinate r ι i∈P := by
  let f : Poly K →+* SeedRing r ι ⧸ P := (Ideal.Quotient.mk P).comp (quotientMap r ι)
  have hH : f (smoothH ι)=0 := by
    have hh : quotientMap r ι (smoothH ι)=0 := Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (by simp [equationsIdeal]))
    change Ideal.Quotient.mk P (quotientMap r ι (smoothH ι))=0
    rw [hh,map_zero]
  have hb0 : f (C r*X 1*X 3)=0 := Ideal.Quotient.eq_zero_iff_mem.mpr hb
  have hd0 : f (X 2^2)=0 := Ideal.Quotient.eq_zero_iff_mem.mpr hd
  have hgen : ∀ j : Fin 5, f (linkageGenerator s r j)=0 := fun j =>
    Ideal.Quotient.eq_zero_iff_mem.mpr (hE (linkageGenerator_mem s r ι j))
  have hz : ∀ i : Fin 5, f (X i)=0 :=
    @variables_zero_of_vertex K _ s r ι hr hι hι1 (SeedRing r ι ⧸ P) _ _ f hb0 hd0 hgen hH
  intro i
  exact Ideal.Quotient.eq_zero_iff_mem.mp (hz i)

theorem mapped_vertex_cover (s : Side) (r ι : K)
    (hr : r≠0) (hι : ι≠0) (hι1 : ι≠1)
    {S : Type*} [CommRing S] (φ : SeedRing r ι →+* S)
    (hcoord : ∃ i : Fin 5, IsUnit (φ (seedCoordinate r ι i))) :
    (linkageIdeal s r ι).map φ ⊔ Ideal.span {φ (linkageB r ι),φ (linkageD r ι)}=⊤ := by
  by_contra hne
  obtain ⟨M,hM,hJM⟩ := Ideal.exists_le_maximal
    ((linkageIdeal s r ι).map φ ⊔ Ideal.span {φ (linkageB r ι),φ (linkageD r ι)}) hne
  letI : M.IsMaximal := hM
  have hE : linkageIdeal s r ι≤M.comap φ := by
    intro q hq
    exact hJM ((le_sup_left : (linkageIdeal s r ι).map φ ≤ _) (Ideal.mem_map_of_mem φ hq))
  have hb : linkageB r ι∈M.comap φ :=
    hJM ((le_sup_right : Ideal.span {φ (linkageB r ι),φ (linkageD r ι)} ≤ _) (Ideal.subset_span (by simp)))
  have hd : linkageD r ι∈M.comap φ :=
    hJM ((le_sup_right : Ideal.span {φ (linkageB r ι),φ (linkageD r ι)} ≤ _) (Ideal.subset_span (by simp)))
  obtain ⟨i,hi⟩ := hcoord
  have hz := seedCoordinates_mem_of_vertex s r ι hr hι hι1 (M.comap φ) hE hb hd i
  exact hM.ne_top (M.eq_top_of_isUnit_mem hz hi)

theorem coordinate_isUnit (r ι : K) (t : Finset (Fin 3)) (i : Fin 3) (hi : i∈t) :
    IsUnit (algebraMap (SeedRing r ι) (SeedLocal K r ι t)
      (seedCoordinate r ι (remainingIndex i))) := by
  have hu := seedProduct_isUnit K r ι (show ({i} : Finset (Fin 3))⊆t by simpa using hi)
  simp only [baseProduct,Finset.prod_singleton] at hu
  change IsUnit (algebraMap (SeedRing r ι) (SeedLocal K r ι t)
    (quotientMap r ι (remainingInclusion K (X i)))) at hu
  simpa only [remainingInclusion,rename_X,seedCoordinate] using hu

theorem localized_vertex_cover (s : Side) (r ι : K)
    (hr : r≠0) (hι : ι≠0) (hι1 : ι≠1)
    (t : Finset (Fin 3)) (ht : t.Nonempty) :
    (linkageIdeal s r ι).map (algebraMap (SeedRing r ι) (SeedLocal K r ι t)) ⊔
      Ideal.span {algebraMap (SeedRing r ι) (SeedLocal K r ι t) (linkageB r ι),
        algebraMap (SeedRing r ι) (SeedLocal K r ι t) (linkageD r ι)}=⊤ := by
  let φ : SeedRing r ι →+* SeedLocal K r ι t :=
    algebraMap (SeedRing r ι) (SeedLocal K r ι t)
  have hcoord : ∃ i : Fin 5, IsUnit (φ (seedCoordinate r ι i)) := by
    obtain ⟨i,hi⟩ := ht
    exact ⟨remainingIndex i,coordinate_isUnit r ι t i hi⟩
  exact @mapped_vertex_cover K (inferInstance : Field K) s r ι hr hι hι1
    (SeedLocal K r ι t) (inferInstance : CommRing (SeedLocal K r ι t)) φ hcoord

end CycleQ2SeedLinkageOrbitCover

#print axioms CycleQ2SeedLinkageOrbitCover.localized_vertex_cover
end
end

/- Component: continuation_3/cylinder_bridge/SegreFactorChartExact.lean -/
section
/-! # Factor exactness on the actual complex coordinate charts

Every hypothesis of the factor sequence is discharged for the literal
smooth incidence seed at r=57 and i=sqrt(-1). The two modules are the
actual localized linkage ideals.
-/

noncomputable section
set_option maxHeartbeats 300000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SegreFactorChartExact

open Matrix CycleQ2IncidenceFirstOrder CycleQ2SegreTangentLocal
  CycleQ2SeedQuotientFiniteFree CycleQ2SeedCechLocalization
  CycleQ2SeedCechLocalizedBasis CycleQ2SeedLinkageIdeals
  CycleQ2SegreFactorSequence

abbrev Chart (s : Finset (Fin 3)) := SeedLocal ℂ 57 Complex.I s

def chartMap (s : Finset (Fin 3)) : SeedRing (57:ℂ) Complex.I →+* Chart s :=
  algebraMap (SeedRing (57:ℂ) Complex.I) (Chart s)

def leftIdeal (s : Finset (Fin 3)) : Ideal (Chart s) :=
  (linkageIdeal .left (57:ℂ) Complex.I).map (chartMap s)

def rightIdeal (s : Finset (Fin 3)) : Ideal (Chart s) :=
  (linkageIdeal .right (57:ℂ) Complex.I).map (chartMap s)

def leftSection (s : Finset (Fin 3)) (i : Fin 3) : Chart s :=
  chartMap s (CycleQ2SeedLinkagePrincipal.leftSection (57:ℂ) Complex.I i)

def rightSection (s : Finset (Fin 3)) (j : Fin 3) : Chart s :=
  chartMap s (CycleQ2SeedLinkagePrincipal.rightSection (57:ℂ) Complex.I j)

def linkage (s : Finset (Fin 3)) : Chart s :=
  chartMap s (CycleQ2SeedLinkagePrincipal.linkage (57:ℂ) Complex.I)

theorem linkage_regular (s : Finset (Fin 3)) :
    Function.Injective (fun z : Chart s => linkage s*z) := by
  apply CycleQ2LinkageIdealPrincipal.localization_mul_injective
    (Algebra.algebraMapSubmonoid (SeedRing (57:ℂ) Complex.I)
      (Submonoid.powers (baseProduct ℂ s))) (Chart s)
    (CycleQ2SeedLinkagePrincipal.linkage (57:ℂ) Complex.I)
  apply CycleQ2SeedLinkageRegular.linkage_mul_injective
  intro h
  have hh := congrArg Complex.im h
  norm_num at hh

theorem chart_ideals_pairing (s : Finset (Fin 3)) :
    leftIdeal s*rightIdeal s≤Ideal.span {linkage s} := by
  dsimp only [leftIdeal,rightIdeal,linkage]
  exact @CycleQ2SeedLinkagePrincipal.mapped_ideals_pairing ℂ inferInstance
    (Chart s) inferInstance (57:ℂ) Complex.I (chartMap s)

def factorData (s : Finset (Fin 3)) (hs : s.Nonempty) : FactorData (Chart s) where
  leftIdeal := leftIdeal s
  rightIdeal := rightIdeal s
  linkage := linkage s
  matrix := CycleQ2SegreComplexChartExact.chartMatrix s
  left := leftSection s
  right := rightSection s
  left_mem i := Ideal.mem_map_of_mem (chartMap s)
    (CycleQ2SeedLinkagePrincipal.leftSection_mem (57:ℂ) Complex.I i)
  right_mem j := Ideal.mem_map_of_mem (chartMap s)
    (CycleQ2SeedLinkagePrincipal.rightSection_mem (57:ℂ) Complex.I j)
  product i j := by
    have h := congrArg (chartMap s)
      (CycleQ2SeedLinkagePrincipal.selected_product (57:ℂ) Complex.I i j)
    simpa only [map_mul,leftSection,rightSection,linkage,
      CycleQ2SegreComplexChartExact.chartMatrix,CycleQ2SegreComplexBasepoint.matrix,
      RingHom.mapMatrix_apply,Matrix.map_apply,chartMap] using h
  ideals_product := chart_ideals_pairing s
  regular := linkage_regular s
  cofactors_zero := CycleQ2SegreComplexChartExact.chartMatrix_cofactors s
  entries_generate := CycleQ2SegreComplexChartExact.chartMatrix_entries_generate s hs

abbrev FactorSections (s : Finset (Fin 3)) :=
  (Fin 3 → leftIdeal s) × (Fin 3 → rightIdeal s)

def chartFactorMap (s : Finset (Fin 3)) (hs : s.Nonempty) :
    FactorSections s →ₗ[Chart s] Matrix (Fin 3) (Fin 3) (Chart s) :=
  factorMap (factorData s hs)

def chartGaugeMap (s : Finset (Fin 3)) (hs : s.Nonempty) :
    Chart s →ₗ[Chart s] FactorSections s := gaugeMap (factorData s hs)

theorem chartFactorMap_formula (s : Finset (Fin 3)) (hs : s.Nonempty)
    (v : FactorSections s) (i j : Fin 3) :
    linkage s*chartFactorMap s hs v i j=
      (v.1 i:Chart s)*rightSection s j+leftSection s i*(v.2 j:Chart s) :=
  linkage_factorMap (factorData s hs) v i j

/-- The literal local short exact factor sequence, without a rank,
local-pivot, ideal-pairing or regularity hypothesis. -/
theorem actual_factor_sequence (s : Finset (Fin 3)) (hs : s.Nonempty) :
    Function.Injective (chartGaugeMap s hs) ∧
    LinearMap.ker (chartFactorMap s hs)=LinearMap.range (chartGaugeMap s hs) ∧
    LinearMap.range (chartFactorMap s hs)=
      LinearMap.ker (cofactorDifferentialLinear (CycleQ2SegreComplexChartExact.chartMatrix s)) :=
  ⟨gaugeMap_injective (factorData s hs),
    ker_factorMap_eq_range_gaugeMap (factorData s hs),
    range_factorMap_eq_ker_differential (factorData s hs)⟩

end CycleQ2SegreFactorChartExact

#print axioms CycleQ2SegreFactorChartExact.linkage_regular
#print axioms CycleQ2SegreFactorChartExact.actual_factor_sequence
end
end

/- Component: continuation_3/cylinder_bridge/SegreLinkageImage.lean -/
section
/-! The actual regular linkage pairing identifies the right factor ideal
with the actual matrix image.  The three selected generators become the
literal columns; surjectivity and injectivity follow from the same
unit-ideal reconstruction that proved perfect duality. -/

noncomputable section
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SegreLinkageImage
open Matrix CycleQ2SegreFactorSequence CycleQ2SegreLinkageDuality

variable {A : Type*} [CommRing A] (F : FactorData A)

def imageMap : F.rightIdeal →ₗ[A] (Fin 3 → A) where
  toFun y i := pairing F y (leftElement F i)
  map_add' y z := by
    funext i
    exact LinearMap.congr_fun ((pairing F).map_add y z) (leftElement F i)
  map_smul' c y := by
    funext i
    exact LinearMap.congr_fun ((pairing F).map_smul c y) (leftElement F i)

theorem imageMap_selected (j : Fin 3) :
    imageMap F (rightElement F j)=F.matrix.col j := by
  funext i
  exact pairing_selected F i j

theorem right_reconstruction_ideal (y : F.rightIdeal) :
    y=∑ q, (weights F q*pairing F y (leftElement F q.1)) • rightElement F q.2 := by
  apply Subtype.ext
  simpa only [Submodule.coe_sum,Submodule.coe_smul,smul_eq_mul,rightElement] using
    right_reconstruction F y

theorem imageMap_injective : Function.Injective (imageMap F) := by
  intro y z he
  rw [right_reconstruction_ideal F y,right_reconstruction_ideal F z]
  apply Finset.sum_congr rfl
  intro q _
  have hh := congrFun he q.1
  change pairing F y (leftElement F q.1)=pairing F z (leftElement F q.1) at hh
  rw [hh]

theorem range_imageMap : LinearMap.range (imageMap F)=LinearMap.range F.matrix.mulVecLin := by
  rw [Matrix.range_mulVecLin]
  apply le_antisymm
  · rintro _ ⟨y,rfl⟩
    rw [right_reconstruction_ideal F y,map_sum]
    apply Submodule.sum_mem
    intro q _
    rw [map_smul,imageMap_selected]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self q.2))
  · apply Submodule.span_le.mpr
    rintro _ ⟨j,rfl⟩
    exact ⟨rightElement F j,imageMap_selected F j⟩

def rightEquivImage : F.rightIdeal ≃ₗ[A] LinearMap.range F.matrix.mulVecLin :=
  (LinearEquiv.ofInjective (imageMap F) (imageMap_injective F)).trans
    (LinearEquiv.ofEq _ _ (range_imageMap F))

theorem rightEquivImage_apply (y : F.rightIdeal) (i : Fin 3) :
    (rightEquivImage F y).val i=pairing F y (leftElement F i) := rfl

theorem rightEquivImage_selected (j : Fin 3) :
    (rightEquivImage F (rightElement F j)).val=F.matrix.col j :=
  imageMap_selected F j

end CycleQ2SegreLinkageImage

#print axioms CycleQ2SegreLinkageImage.rightEquivImage
#print axioms CycleQ2SegreLinkageImage.rightEquivImage_selected
end
end
