import Proposal.PhysicalJacobianCoordinates
import Proposal.PhysicalCubicJets
import Proposal.JacobianSource

/-! Embedding the exact Jacobian function field in the physical sextic
function field. The monic-root embedding and derivation compatibility are
the shared HoldoutCover constructions, credited to fqlx and collaborators.
Prepared with OpenAI Codex assistance. -/
noncomputable section
namespace CyclePhysicalJacobianMap
open HoldoutConstruction CyclePhysical CyclePhysicalCoordinates
open CyclePhysicalJacobianCoordinates CyclePhysicalCubicJets
open CycleCubicFieldDifferential.Physical
open scoped BigOperators
local instance : Algebra ℤ FunctionField := Ring.toIntAlgebra _

def constantMap : ℂ →+* FunctionField := residueMap.comp MvPolynomial.C
def coefficientMap : CycleJacobianDomain.Coeff →+* FunctionField :=
  MvPolynomial.eval₂Hom constantMap passive
lemma coefficientMap_injective : Function.Injective coefficientMap :=
  coefficient_evaluation_injective
@[simp] lemma coefficientMap_C (c : ℂ) : coefficientMap (MvPolynomial.C c)=constantMap c :=
  MvPolynomial.eval₂Hom_C _ _ _
@[simp] lemma coefficientMap_X (i : Fin 5) : coefficientMap (MvPolynomial.X i)=passive i :=
  MvPolynomial.eval₂Hom_X' _ _ _

lemma a8_scaling : CycleJacobian.a8 cOne cTwo 1 radial targetTime=8*radial^4*aWeierstrass := by
  simp only [CycleJacobian.a8,targetTime,aWeierstrass,CycleCubic.s4,
    coeffA,coeffB,coeffC,coeffD,coeffE,coeffF,t]
  ring
lemma b256_scaling :
    CycleJacobian.b256 cOne cTwo 1 radial targetTime=256*radial^6*bWeierstrass := by
  simp only [CycleJacobian.b256,targetTime,bWeierstrass,CycleCubic.s6,
    coeffA,coeffB,coeffC,coeffD,coeffE,coeffF,t]
  ring
lemma coefficient_rhs : coefficientMap CycleJacobianDomain.rhs=
    targetX^3+(1/8)*CycleJacobian.a8 cOne cTwo 1 radial targetTime*targetX+
      (1/256)*CycleJacobian.b256 cOne cTwo 1 radial targetTime := by
  simp only [CycleJacobianDomain.rhs,CycleJacobian.a8,CycleJacobian.b256,
    map_add,map_sub,map_mul,map_pow,map_neg,map_one,map_ofNat,
    coefficientMap_C,coefficientMap_X]
  norm_num [passive,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
    Matrix.head_cons,Matrix.tail_cons,map_div₀,map_ofNat]
lemma physical_root : CycleJacobianDomain.equation.eval₂ coefficientMap targetY=0 := by
  rw [CycleJacobianDomain.equation,Polynomial.eval₂_sub,Polynomial.eval₂_pow,
    Polynomial.eval₂_X,Polynomial.eval₂_C,coefficient_rhs,a8_scaling,b256_scaling]
  simp only [targetX,targetY]
  linear_combination radial^6*curve

def ringMap : CycleJacobianEmbedding.TargetRing →+* FunctionField :=
  AdjoinRoot.lift (f:=CycleJacobianDomain.equation) coefficientMap targetY physical_root
lemma ringMap_injective : Function.Injective ringMap :=
  monic_root_embedding_injective CycleJacobianDomain.equation
    CycleJacobianDomain.equation_monic CycleJacobianDomain.equation_irreducible
    coefficientMap coefficientMap_injective targetY physical_root
def fieldMap : CycleJacobianEmbedding.TargetField →+* FunctionField :=
  IsFractionRing.lift ringMap_injective
lemma fieldMap_ring (r : CycleJacobianEmbedding.TargetRing) :
    fieldMap (algebraMap CycleJacobianEmbedding.TargetRing CycleJacobianEmbedding.TargetField r)=
      ringMap r := IsFractionRing.lift_algebraMap ringMap_injective r

def coordinates : Fin 6 → FunctionField := Fin.cons targetY passive
@[simp] lemma coordinates_zero : coordinates 0=targetY := rfl
@[simp] lemma coordinates_one : coordinates 1=targetTime := rfl
@[simp] lemma coordinates_two : coordinates 2=cOne := rfl
@[simp] lemma coordinates_three : coordinates 3=cTwo := rfl
@[simp] lemma coordinates_four : coordinates 4=radial := rfl
@[simp] lemma coordinates_five : coordinates 5=targetX := rfl

def evaluation : CycleJacobianHypersurface.Ambient →+* FunctionField :=
  MvPolynomial.eval₂Hom constantMap coordinates
@[simp] lemma evaluation_C (c : ℂ) : evaluation (MvPolynomial.C c)=constantMap c :=
  MvPolynomial.eval₂Hom_C _ _ _
@[simp] lemma evaluation_X (i : Fin 6) : evaluation (MvPolynomial.X i)=coordinates i :=
  MvPolynomial.eval₂Hom_X' _ _ _
lemma fieldMap_residue (p : CycleJacobianHypersurface.Ambient) :
    fieldMap (CycleJacobianHypersurface.residueMap p)=evaluation p := by
  have hm : fieldMap.comp CycleJacobianHypersurface.residueMap=evaluation := by
    apply MvPolynomial.ringHom_ext
    · intro z
      change fieldMap (algebraMap CycleJacobianEmbedding.TargetRing CycleJacobianEmbedding.TargetField
        (AdjoinRoot.mk _ (MvPolynomial.finSuccEquiv ℂ 5 (MvPolynomial.C z))))=_
      rw [fieldMap_ring,CycleJacobianHypersurface.finSucc_C]
      rw [evaluation_C]
      change AdjoinRoot.lift coefficientMap targetY physical_root
        (AdjoinRoot.of _ (MvPolynomial.C z))=constantMap z
      rw [AdjoinRoot.lift_of,coefficientMap_C]
    · intro i
      change fieldMap (algebraMap CycleJacobianEmbedding.TargetRing CycleJacobianEmbedding.TargetField
        (AdjoinRoot.mk _ (MvPolynomial.finSuccEquiv ℂ 5 (MvPolynomial.X i))))=_
      rw [fieldMap_ring,evaluation_X]
      refine Fin.cases ?_ (fun j => ?_) i
      · rw [MvPolynomial.finSuccEquiv_X_zero]
        exact AdjoinRoot.lift_root _
      · rw [MvPolynomial.finSuccEquiv_X_succ]
        change AdjoinRoot.lift coefficientMap targetY physical_root
          (AdjoinRoot.of _ (MvPolynomial.X j))=passive j
        rw [AdjoinRoot.lift_of,coefficientMap_X]
  exact congrArg (fun f : CycleJacobianHypersurface.Ambient →+* FunctionField => f p) hm

lemma evaluation_hypersurface : evaluation CycleJacobianHypersurface.hypersurface=0 := by
  rw [← fieldMap_residue,
    (CycleJacobianHypersurface.residueMap_kernel _).mpr (dvd_refl _),map_zero]
lemma evaluation_normal : evaluation (MvPolynomial.pderiv 0 CycleJacobianHypersurface.hypersurface)=
    2*targetY := by
  rw [CycleJacobianHypersurface.normal_polynomial]
  simp only [map_mul,map_ofNat,evaluation_X,coordinates_zero]
lemma evaluation_second_normal :
    evaluation (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0 CycleJacobianHypersurface.hypersurface))=2 := by
  have h2 : MvPolynomial.pderiv 0 (2:CycleJacobianHypersurface.Ambient)=0 :=
    (MvPolynomial.pderiv 0).map_natCast 2
  rw [CycleJacobianHypersurface.normal_polynomial]
  simp [MvPolynomial.pderiv_mul,MvPolynomial.pderiv_X,h2,map_ofNat]

lemma derivative_evaluation (j : Fin 5) (p : CycleJacobianHypersurface.Ambient) :
    coordinateDerivation j (evaluation p)=
      evaluation (MvPolynomial.pderiv 0 p)*coordinateDerivation j targetY+
      evaluation (MvPolynomial.pderiv j.succ p) := by
  have hc (c : ℂ) : coordinateDerivation j (constantMap c)=0 :=
    coordinateDerivation_constant j c
  rw [evaluation,derivation_eval₂_chain (coordinateDerivation j) constantMap coordinates hc]
  simp [Fin.sum_univ_succ,coordinates,coordinateDerivation_passive,mul_ite,evaluation]
lemma derivative_targetY (j : Fin 5) : coordinateDerivation j targetY=
    -evaluation (MvPolynomial.pderiv j.succ CycleJacobianHypersurface.hypersurface)/(2*targetY) := by
  have h := congrArg (coordinateDerivation j) evaluation_hypersurface
  rw [map_zero,derivative_evaluation,evaluation_normal] at h
  have hy := targetY_nonzero
  field_simp
  linear_combination h

lemma tangent_polynomial (j : Fin 5) (p : CycleJacobianHypersurface.Ambient) :
    coordinateDerivation j (fieldMap (CycleJacobianHypersurface.residueMap p))=
      fieldMap (CycleJacobianHypersurface.tangent j (CycleJacobianHypersurface.residueMap p)) := by
  rw [fieldMap_residue,derivative_evaluation,derivative_targetY,CycleJacobianHypersurface.tangent_apply]
  simp only [map_sub,map_mul,map_div₀,fieldMap_residue,evaluation_normal]
  ring
theorem tangent_compatible (j : Fin 5) (z : CycleJacobianEmbedding.TargetField) :
    coordinateDerivation j (fieldMap z)=fieldMap (CycleJacobianHypersurface.tangent j z) :=
  derivation_intertwines_quotient_fraction CycleJacobianHypersurface.projection
    CycleJacobianHypersurface.projection_surjective fieldMap
    (CycleJacobianHypersurface.tangent j) (coordinateDerivation j)
    (fun c => tangent_polynomial j (MvPolynomial.C c))
    (fun i => tangent_polynomial j (MvPolynomial.X i)) z

lemma evaluation_source : evaluation CycleJacobianSource.source=
    radial^5/144*(aDot*xi+bDot) := by
  simp only [CycleJacobianSource.source,CycleJacobianSource.sourceNumerator,
    map_add,map_sub,map_mul,map_pow,map_ofNat,evaluation_X,evaluation_C]
  simp only [coordinates_zero,coordinates_one,coordinates_two,coordinates_three,
    coordinates_four,coordinates_five,map_div₀,map_ofNat,map_one]
  simp only [targetTime,targetX,aDot_formula,bDot_formula,
    coeffA,coeffB,coeffC,coeffD,coeffE,coeffF,t]
  ring
lemma source_normal : MvPolynomial.pderiv 0 CycleJacobianSource.source=0 := by
  have h2 : MvPolynomial.pderiv 0 (2:CycleJacobianHypersurface.Ambient)=0 :=
    (MvPolynomial.pderiv 0).map_natCast 2
  have h32 : MvPolynomial.pderiv 0 (32:CycleJacobianHypersurface.Ambient)=0 :=
    (MvPolynomial.pderiv 0).map_natCast 32
  have h48 : MvPolynomial.pderiv 0 (48:CycleJacobianHypersurface.Ambient)=0 :=
    (MvPolynomial.pderiv 0).map_natCast 48
  have h3456 : MvPolynomial.pderiv 0 (3456:CycleJacobianHypersurface.Ambient)=0 :=
    (MvPolynomial.pderiv 0).map_natCast 3456
  norm_num [CycleJacobianSource.source,CycleJacobianSource.sourceNumerator,
    MvPolynomial.pderiv_mul,MvPolynomial.pderiv_pow,MvPolynomial.pderiv_X,
    Pi.single_apply,Fin.ext_iff,h2,h32,h48,h3456]

theorem mapped_source_solution : ∃ w : Fin 5 → FunctionField,
    residueDivergence coordinateDerivation (2*targetY) w=
      (aDot*xi+bDot)/(288*radial*eta^2) := by
  obtain ⟨w,hw⟩ := CycleJacobianSource.source_residue_solution
  refine ⟨fun i => fieldMap (w i),?_⟩
  have h := residueDivergence_map fieldMap CycleJacobianHypersurface.tangent
    coordinateDerivation tangent_compatible
    (CycleJacobianHypersurface.residueMap (MvPolynomial.pderiv 0 CycleJacobianHypersurface.hypersurface)) w
  rw [hw] at h
  simp only [map_neg,map_sub,map_div₀,map_mul,map_pow,fieldMap_residue,
    evaluation_normal,evaluation_second_normal,source_normal,map_zero,zero_div,
    zero_sub,neg_neg,evaluation_source] at h
  rw [h]
  have hr := radial_ne_zero
  have hy := CyclePhysicalCubicJets.eta_nonzero
  unfold targetY
  field_simp
  ring

end CyclePhysicalJacobianMap
#print axioms CyclePhysicalJacobianMap.fieldMap_residue
#print axioms CyclePhysicalJacobianMap.mapped_source_solution
