import Proposal.GenericQ2
import Proposal.HoldoutCoefficientMap
import Proposal.EndpointTarget

/-! Substituting the passive ratios into the fully generic cubic certificate.
The numerator scalar is exactly alpha³ beta² / 2.  The degree-27 norm
 denominator is unchanged, including its good-fiber legality certificate. -/
noncomputable section
namespace HoldoutQ2.PassiveQ2
open MvPolynomial HodgeTestbed Clearing CoefficientMap

abbrev Poly (k : ℂ) := MvPolynomial (Fin 4) (Regular k)

def coefficientPolynomialMap (k : ℂ) (hk : k^2+k+1=0) :
    GenericQ2.Poly →+* Poly k := MvPolynomial.map (lineCoefficientMap k hk)

def parameterPolynomialMap (k : ℂ) :
    MvPolynomial (Fin 4) Parameters →+* Poly k :=
  MvPolynomial.map (algebraMap Parameters (Regular k))

def F (k : ℂ) : Poly k := parameterPolynomialMap k (HoldoutEndpointTarget.cubic k)
def source (k : ℂ) : Poly k := parameterPolynomialMap k HoldoutEndpointTarget.source

def weight (k : ℂ) : Regular k := constant k (1/2) * alpha k^3 * beta k^2

def D (k : ℂ) (hk : k^2+k+1=0) : Poly k := coefficientPolynomialMap k hk GenericQ2.D

def N (k : ℂ) (hk : k^2+k+1=0) (i : Fin 4) : Poly k :=
  C (weight k) * coefficientPolynomialMap k hk (GenericQ2.N i)

@[simp] theorem coefficientPolynomialMap_X (k : ℂ) (hk : k^2+k+1=0) (i : Fin 4) :
    coefficientPolynomialMap k hk (X i)=X i := MvPolynomial.map_X _ _

@[simp] theorem coefficientPolynomialMap_C (k : ℂ) (hk : k^2+k+1=0)
    (r : GenericQ2.K) :
    coefficientPolynomialMap k hk (C r)=C (lineCoefficientMap k hk r) :=
  MvPolynomial.map_C _ _

@[simp] theorem coefficientPolynomialMap_F (k : ℂ) (hk : k^2+k+1=0) :
    coefficientPolynomialMap k hk GenericQ2.F=F k := by
  simp only [GenericQ2.F,GenericQuadratic.F,HodgeComputer.CubicSurfaces.LineContact.cubic,
    F,parameterPolynomialMap,HoldoutEndpointTarget.cubic,HoldoutAlgebra.cubic,
    map_add,map_sub,map_mul,map_pow,map_ofNat,coefficientPolynomialMap_X,
    coefficientPolynomialMap_C,lineCoefficientMap_a,lineCoefficientMap_b,
    lineCoefficientMap_c,lineCoefficientMap_d,MvPolynomial.map_X,MvPolynomial.map_C,
    alpha,beta,constant,map_one]

@[simp] theorem coefficientPolynomialMap_B (k : ℂ) (hk : k^2+k+1=0) :
    coefficientPolynomialMap k hk GenericQ2.B=(X 0 : Poly k)^3*X 1^2 := by
  simp only [GenericQ2.B,map_mul,map_pow,coefficientPolynomialMap_X]

theorem source_eq (k : ℂ) : source k=C (weight k)*(X 0 : Poly k)^3*X 1^2 := by
  simp only [source,parameterPolynomialMap,HoldoutEndpointTarget.source,
    map_mul,map_pow,MvPolynomial.map_X,MvPolynomial.map_C,weight,constant,alpha,beta]

@[simp] theorem coefficientPolynomialMap_pderiv (k : ℂ) (hk : k^2+k+1=0)
    (i : Fin 4) (P : GenericQ2.Poly) :
    coefficientPolynomialMap k hk (pderiv i P)=pderiv i (coefficientPolynomialMap k hk P) :=
  MvPolynomial.pderiv_map.symm

@[simp] theorem coefficientPolynomialMap_directional (k : ℂ) (hk : k^2+k+1=0)
    (P : GenericQ2.Poly) (V : Fin 4 → GenericQ2.Poly) :
    coefficientPolynomialMap k hk (directional P V)=
      directional (coefficientPolynomialMap k hk P) (fun i => coefficientPolynomialMap k hk (V i)) := by
  simp only [directional,map_sum,map_mul,coefficientPolynomialMap_pderiv]

@[simp] theorem coefficientPolynomialMap_divergence (k : ℂ) (hk : k^2+k+1=0)
    (V : Fin 4 → GenericQ2.Poly) :
    coefficientPolynomialMap k hk (divergence V)=
      divergence (fun i => coefficientPolynomialMap k hk (V i)) := by
  simp only [divergence,map_sum,coefficientPolynomialMap_pderiv]

@[simp] theorem coefficientPolynomialMap_divergenceNumerator (k : ℂ) (hk : k^2+k+1=0)
    (P : GenericQ2.Poly) (V : Fin 4 → GenericQ2.Poly) :
    coefficientPolynomialMap k hk (divergenceNumerator P V)=
      divergenceNumerator (coefficientPolynomialMap k hk P)
        (fun i => coefficientPolynomialMap k hk (V i)) := by
  simp only [divergenceNumerator,map_sub,map_mul,coefficientPolynomialMap_divergence,
    coefficientPolynomialMap_directional]

theorem F_homogeneous (k : ℂ) (hk : k^2+k+1=0) : (F k).IsHomogeneous 3 := by
  rw [← coefficientPolynomialMap_F k hk]
  exact GenericQ2.F_homogeneous.map _

theorem D_homogeneous (k : ℂ) (hk : k^2+k+1=0) : (D k hk).IsHomogeneous 27 :=
  GenericQ2.D_homogeneous.map _

theorem N_homogeneous (k : ℂ) (hk : k^2+k+1=0) (i : Fin 4) :
    (N k hk i).IsHomogeneous 30 :=
  ((GenericQ2.N_homogeneous i).map _).C_mul (weight k)

/-- Nonvanishing survives the noninjective coefficient substitution, because the
norm specializes to one on the S-axis, independently of every parameter. -/
theorem D_axis (k : ℂ) (hk : k^2+k+1=0) :
    MvPolynomial.eval ![0,0,1,0] (D k hk)=(6 : Regular k) := by
  unfold D coefficientPolynomialMap
  rw [MvPolynomial.eval_map]
  change MvPolynomial.eval₂Hom (lineCoefficientMap k hk) ![0,0,1,0] GenericQ2.D = _
  rw [GenericQ2.D_eq,map_mul]
  simp only [eval₂Hom_C,map_ofNat]
  unfold GenericQuadratic.D
  rw [QuadraticSolver.denominator_eval₂]
  simp

theorem D_ne_zero (k : ℂ) (hk : k^2+k+1=0) : D k hk≠0 := by
  intro hz
  have he := congrArg (MvPolynomial.eval ![0,0,1,0]) hz
  rw [D_axis,map_zero] at he
  have h := congrArg (RegularSpecialization.specialize (goodParameters k)) he
  norm_num [map_ofNat] at h

/-- The exact q=2 source and strict divergence equations for the passive cubic. -/
theorem equations (k : ℂ) (hk : k^2+k+1=0) :
    2*directional (F k) (N k hk)=source k*D k hk ∧
      divergenceNumerator (D k hk) (N k hk)=0 := by
  have hs := congrArg (coefficientPolynomialMap k hk) GenericQ2.equations.1
  simp only [map_mul,map_ofNat,coefficientPolynomialMap_directional,
    coefficientPolynomialMap_F,coefficientPolynomialMap_B] at hs
  have hd := congrArg (coefficientPolynomialMap k hk) GenericQ2.equations.2
  simp only [coefficientPolynomialMap_divergenceNumerator,map_zero] at hd
  constructor
  · unfold N
    rw [directional_mul,source_eq]
    change 2*(C (weight k)*directional (F k) (fun i => coefficientPolynomialMap k hk (GenericQ2.N i))) =
      C (weight k)*X 0^3*X 1^2*coefficientPolynomialMap k hk GenericQ2.D
    linear_combination C (weight k)*hs
  · unfold N divergenceNumerator
    rw [HodgeComputer.CubicSurfaces.Q2Reduction.divergence_C_mul,directional_mul]
    change coefficientPolynomialMap k hk GenericQ2.D *
      (C (weight k)*divergence (fun i => coefficientPolynomialMap k hk (GenericQ2.N i))) -
      C (weight k)*directional (coefficientPolynomialMap k hk GenericQ2.D)
        (fun i => coefficientPolynomialMap k hk (GenericQ2.N i))=0
    unfold divergenceNumerator at hd
    linear_combination C (weight k)*hd

theorem certificate (k : ℂ) (hk : k^2+k+1=0) :
    D k hk≠0 ∧ (D k hk).IsHomogeneous 27 ∧
      (∀ i, (N k hk i).IsHomogeneous 30) ∧
      2*directional (F k) (N k hk)=source k*D k hk ∧
      divergenceNumerator (D k hk) (N k hk)=0 :=
  ⟨D_ne_zero k hk,D_homogeneous k hk,N_homogeneous k hk,equations k hk⟩

end HoldoutQ2.PassiveQ2
#print axioms HoldoutQ2.PassiveQ2.certificate
