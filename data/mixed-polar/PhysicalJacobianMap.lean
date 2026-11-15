import Proposal.PhysicalJacobianCoordinates
import Proposal.PhysicalCubicJets
import Proposal.PhysicalJacobianCoefficients
import Proposal.JacobianSource

/-! Embedding the exact Jacobian function field in the physical sextic
function field. The monic-root embedding and derivation compatibility are
the shared HoldoutCover constructions, credited to fqlx and collaborators.
Adapted to the actual mixed-polar quadratic extension with Codex assistance.
Every coefficient and source is bound to the exact fixed target. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
namespace MixedPolarPhysicalJacobianMap
open HoldoutConstruction MixedPolarPhysical MixedPolarPhysicalCoordinates
open MixedPolarPhysicalJacobianCoordinates MixedPolarPhysicalCubicJets
open MixedPolarPhysicalShear MixedPolarPhysicalTangent
open scoped BigOperators
local instance : Algebra ℤ Extension := Ring.toIntAlgebra _

def constantMap : ℂ →+* Extension := (ι.comp residueMap).comp MvPolynomial.C
def coefficientMap : MixedPolarJacobianDomain.Coeff →+* Extension :=
  MvPolynomial.eval₂Hom constantMap passive
lemma coefficientMap_injective : Function.Injective coefficientMap :=
  by simpa only [coefficientMap,constantMap,RingHom.comp_assoc] using coefficient_evaluation_injective
@[simp] lemma coefficientMap_C (c : ℂ) : coefficientMap (MvPolynomial.C c)=constantMap c :=
  MvPolynomial.eval₂Hom_C _ _ _
@[simp] lemma coefficientMap_X (i : Fin 5) : coefficientMap (MvPolynomial.X i)=passive i :=
  MvPolynomial.eval₂Hom_X' _ _ _

lemma a8_scaling : MixedPolarJacobian.a8 (ι cOne) (ι cTwo) 1 (ι radial) targetTime=432*(ι radial)^4*aWeierstrass := by
  simpa only [targetTime,aWeierstrass] using MixedPolarPhysicalJacobianCoefficients.a8_scaling
lemma b256_scaling :
    MixedPolarJacobian.b256 (ι cOne) (ι cTwo) 1 (ι radial) targetTime=432*(ι radial)^6*bWeierstrass := by
  simpa only [targetTime,bWeierstrass] using MixedPolarPhysicalJacobianCoefficients.b256_scaling
lemma coefficient_rhs : coefficientMap MixedPolarJacobianDomain.rhs=
    targetX^3+(1/432)*MixedPolarJacobian.a8 (ι cOne) (ι cTwo) 1 (ι radial) targetTime*targetX+
      (1/432)*MixedPolarJacobian.b256 (ι cOne) (ι cTwo) 1 (ι radial) targetTime := by
  simp only [MixedPolarJacobianDomain.rhs,MixedPolarJacobian.a8,MixedPolarJacobian.b256,
    MixedPolarJacobian.a432,MixedPolarJacobian.b432,
    map_add,map_sub,map_mul,map_pow,map_neg,map_one,map_ofNat,
    coefficientMap_C,coefficientMap_X]
  norm_num [passive,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
    Matrix.head_cons,Matrix.tail_cons,map_div₀,map_ofNat]
lemma physical_root : MixedPolarJacobianDomain.equation.eval₂ coefficientMap targetY=0 := by
  rw [MixedPolarJacobianDomain.equation,Polynomial.eval₂_sub,Polynomial.eval₂_pow,
    Polynomial.eval₂_X,Polynomial.eval₂_C,coefficient_rhs,a8_scaling,b256_scaling]
  simp only [targetX,targetY]
  linear_combination (ι radial)^6*curve

def ringMap : MixedPolarJacobianEmbedding.TargetRing →+* Extension :=
  AdjoinRoot.lift (f:=MixedPolarJacobianDomain.equation) coefficientMap targetY physical_root
lemma ringMap_injective : Function.Injective ringMap :=
  monic_root_embedding_injective MixedPolarJacobianDomain.equation
    MixedPolarJacobianDomain.equation_monic MixedPolarJacobianDomain.equation_irreducible
    coefficientMap coefficientMap_injective targetY physical_root
def fieldMap : MixedPolarJacobianEmbedding.TargetField →+* Extension :=
  IsFractionRing.lift ringMap_injective
lemma fieldMap_ring (r : MixedPolarJacobianEmbedding.TargetRing) :
    fieldMap (algebraMap MixedPolarJacobianEmbedding.TargetRing MixedPolarJacobianEmbedding.TargetField r)=
      ringMap r := IsFractionRing.lift_algebraMap ringMap_injective r

def coordinates : Fin 6 → Extension := Fin.cons targetY passive
@[simp] lemma coordinates_zero : coordinates 0=targetY := rfl
@[simp] lemma coordinates_one : coordinates 1=targetTime := rfl
@[simp] lemma coordinates_two : coordinates 2=ι cOne := rfl
@[simp] lemma coordinates_three : coordinates 3=ι cTwo := rfl
@[simp] lemma coordinates_four : coordinates 4=ι radial := rfl
@[simp] lemma coordinates_five : coordinates 5=targetX := rfl

def evaluation : MixedPolarJacobianHypersurface.Ambient →+* Extension :=
  MvPolynomial.eval₂Hom constantMap coordinates
@[simp] lemma evaluation_C (c : ℂ) : evaluation (MvPolynomial.C c)=constantMap c :=
  MvPolynomial.eval₂Hom_C _ _ _
@[simp] lemma evaluation_X (i : Fin 6) : evaluation (MvPolynomial.X i)=coordinates i :=
  MvPolynomial.eval₂Hom_X' _ _ _
lemma fieldMap_residue (p : MixedPolarJacobianHypersurface.Ambient) :
    fieldMap (MixedPolarJacobianHypersurface.residueMap p)=evaluation p := by
  have hm : fieldMap.comp MixedPolarJacobianHypersurface.residueMap=evaluation := by
    apply MvPolynomial.ringHom_ext
    · intro z
      change fieldMap (algebraMap MixedPolarJacobianEmbedding.TargetRing MixedPolarJacobianEmbedding.TargetField
        (AdjoinRoot.mk _ (MvPolynomial.finSuccEquiv ℂ 5 (MvPolynomial.C z))))=_
      rw [fieldMap_ring,MixedPolarJacobianHypersurface.finSucc_C]
      rw [evaluation_C]
      change AdjoinRoot.lift coefficientMap targetY physical_root
        (AdjoinRoot.of _ (MvPolynomial.C z))=constantMap z
      rw [AdjoinRoot.lift_of,coefficientMap_C]
    · intro i
      change fieldMap (algebraMap MixedPolarJacobianEmbedding.TargetRing MixedPolarJacobianEmbedding.TargetField
        (AdjoinRoot.mk _ (MvPolynomial.finSuccEquiv ℂ 5 (MvPolynomial.X i))))=_
      rw [fieldMap_ring,evaluation_X]
      refine Fin.cases ?_ (fun j => ?_) i
      · rw [MvPolynomial.finSuccEquiv_X_zero]
        exact AdjoinRoot.lift_root _
      · rw [MvPolynomial.finSuccEquiv_X_succ]
        change AdjoinRoot.lift coefficientMap targetY physical_root
          (AdjoinRoot.of _ (MvPolynomial.X j))=passive j
        rw [AdjoinRoot.lift_of,coefficientMap_X]
  exact congrArg (fun f : MixedPolarJacobianHypersurface.Ambient →+* Extension => f p) hm

lemma evaluation_hypersurface : evaluation MixedPolarJacobianHypersurface.hypersurface=0 := by
  rw [← fieldMap_residue,
    (MixedPolarJacobianHypersurface.residueMap_kernel _).mpr (dvd_refl _),map_zero]
lemma evaluation_normal : evaluation (MvPolynomial.pderiv 0 MixedPolarJacobianHypersurface.hypersurface)=
    2*targetY := by
  rw [MixedPolarJacobianHypersurface.normal_polynomial]
  simp only [map_mul,map_ofNat,evaluation_X,coordinates_zero]
lemma evaluation_second_normal :
    evaluation (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0 MixedPolarJacobianHypersurface.hypersurface))=2 := by
  have h2 : MvPolynomial.pderiv 0 (2:MixedPolarJacobianHypersurface.Ambient)=0 :=
    (MvPolynomial.pderiv 0).map_natCast 2
  rw [MixedPolarJacobianHypersurface.normal_polynomial]
  simp [MvPolynomial.pderiv_mul,MvPolynomial.pderiv_X,h2,map_ofNat]

lemma derivative_evaluation (j : Fin 5) (p : MixedPolarJacobianHypersurface.Ambient) :
    coordinateDerivation j (evaluation p)=
      evaluation (MvPolynomial.pderiv 0 p)*coordinateDerivation j targetY+
      evaluation (MvPolynomial.pderiv j.succ p) := by
  have hc (c : ℂ) : coordinateDerivation j (constantMap c)=0 :=
    coordinateDerivation_constant j c
  rw [evaluation,derivation_eval₂_chain (coordinateDerivation j) constantMap coordinates hc]
  simp [Fin.sum_univ_succ,coordinates,coordinateDerivation_passive,mul_ite,evaluation]
lemma derivative_targetY (j : Fin 5) : coordinateDerivation j targetY=
    -evaluation (MvPolynomial.pderiv j.succ MixedPolarJacobianHypersurface.hypersurface)/(2*targetY) := by
  have h := congrArg (coordinateDerivation j) evaluation_hypersurface
  rw [map_zero,derivative_evaluation,evaluation_normal] at h
  have hy := targetY_nonzero
  field_simp
  linear_combination h

lemma tangent_polynomial (j : Fin 5) (p : MixedPolarJacobianHypersurface.Ambient) :
    coordinateDerivation j (fieldMap (MixedPolarJacobianHypersurface.residueMap p))=
      fieldMap (MixedPolarJacobianHypersurface.tangent j (MixedPolarJacobianHypersurface.residueMap p)) := by
  rw [fieldMap_residue,derivative_evaluation,derivative_targetY,MixedPolarJacobianHypersurface.tangent_apply]
  simp only [map_sub,map_mul,map_div₀,fieldMap_residue,evaluation_normal]
  ring
theorem tangent_compatible (j : Fin 5) (z : MixedPolarJacobianEmbedding.TargetField) :
    coordinateDerivation j (fieldMap z)=fieldMap (MixedPolarJacobianHypersurface.tangent j z) :=
  derivation_intertwines_quotient_fraction MixedPolarJacobianHypersurface.projection
    MixedPolarJacobianHypersurface.projection_surjective fieldMap
    (MixedPolarJacobianHypersurface.tangent j) (coordinateDerivation j)
    (fun c => tangent_polynomial j (MvPolynomial.C c))
    (fun i => tangent_polynomial j (MvPolynomial.X i)) z

lemma evaluation_source : evaluation MixedPolarJacobianSource.source=
    ι (cOne*cTwo)*(ι radial)^5/144*(aDot*xi+bDot) := by
  have hs : evaluation MixedPolarJacobianSource.source=
      MixedPolarScaling.jacobianSource (ι cOne) (ι cTwo) (ι radial) targetTime targetX := by
    simp only [MixedPolarJacobianSource.source,MixedPolarJacobianSource.sourceNumerator,
      map_add,map_sub,map_mul,map_pow,map_neg,map_ofNat,evaluation_X,evaluation_C]
    simp only [coordinates_zero,coordinates_one,coordinates_two,coordinates_three,
      coordinates_four,coordinates_five,map_div₀,map_ofNat,map_one,
      MixedPolarScaling.jacobianSource]
    ring
  rw [hs]
  simpa only [targetTime,targetX] using
    MixedPolarPhysicalJacobianCoefficients.jacobian_source_scaling

lemma source_normal : MvPolynomial.pderiv 0 MixedPolarJacobianSource.source=0 :=
  MixedPolarJacobianSource.source_normal

theorem mapped_source_solution : ∃ w : Fin 5 → Extension,
    residueDivergence coordinateDerivation (2*targetY) w=
      ι (cOne*cTwo)*(aDot*xi+bDot)/(288*(ι radial)*eta^2) := by
  obtain ⟨w,hw⟩ := MixedPolarJacobianSource.source_residue_solution
  refine ⟨fun i => fieldMap (w i),?_⟩
  have h := residueDivergence_map fieldMap MixedPolarJacobianHypersurface.tangent
    coordinateDerivation tangent_compatible
    (MixedPolarJacobianHypersurface.residueMap (MvPolynomial.pderiv 0 MixedPolarJacobianHypersurface.hypersurface)) w
  rw [hw] at h
  simp only [map_neg,map_sub,map_div₀,map_mul,map_pow,fieldMap_residue,
    evaluation_normal,evaluation_second_normal,source_normal,map_zero,zero_div,
    zero_sub,neg_neg,evaluation_source] at h
  rw [h]
  have hr := lifted_radial_ne_zero
  have hy := MixedPolarPhysicalCubicJets.eta_nonzero
  unfold targetY
  simp only [map_mul]
  field_simp
  ring

end MixedPolarPhysicalJacobianMap
#print axioms MixedPolarPhysicalJacobianMap.fieldMap_residue
#print axioms MixedPolarPhysicalJacobianMap.mapped_source_solution
