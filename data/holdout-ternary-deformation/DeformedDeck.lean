import Proposal.DeformedCoverCoordinates
import HodgeComputer.Constructions.HoldoutCover.CoverDeckField

/-!
The sixth-root deck action preserves the added ternary deformation because
it fixes X0, X1 and X2. Its inverse-fourth-power character has zero trace.
Uses fqlx's Fermat base automorphisms and generic trace theorem, with a new
invariance proof and field action for the exact deformed cover.
Prepared with OpenAI Codex assistance for hodgepodgeconjecture.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace DeformedCover
open HoldoutConstruction Polynomial
open DeformedConic (BaseField)
local instance deformedDeck_local_1 : Module.Finite PhysicalField CoverField := coverField_physicalFinite
local instance deformedDeck_local_2 : Algebra.IsIntegral PhysicalField CoverField := Algebra.IsIntegral.of_finite PhysicalField CoverField

private lemma alpha_eq : DeformedConic.baseFieldAlpha=genericBaseAlpha ℂ := rfl
private lemma beta_eq : DeformedConic.baseFieldBeta=genericBaseBeta ℂ := rfl

lemma deck_polynomial (z : ℂ) (hz : z^6=1) (hz0 : z ≠ 0) :
    coverPolynomial.map (commonDeckCoefficientEquiv z hz hz0)=coverPolynomial := by
  unfold coverPolynomial DeformedGeometry.coverPolynomial
  rw [alpha_eq,beta_eq,Polynomial.map_add,commonDeck_polynomial]
  congr 1
  simp only [DeformedGeometry.ternaryCorrection,Polynomial.map_add,Polynomial.map_mul,
    Polynomial.map_pow,Polynomial.map_C,Polynomial.map_X,Polynomial.map_ofNat,map_mul,map_pow,map_ofNat,
    RingEquiv.coe_toRingHom,commonDeckCoefficientEquiv_C,commonDeckCoefficientEquiv_X,
    map_inv₀,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons,Matrix.tail_cons]

def deckRingEquiv (z : ℂ) (hz : z^6=1) (hz0 : z ≠ 0) : CoverRing ≃+* CoverRing :=
  AdjoinRoot.mapRingEquiv (commonDeckCoefficientEquiv z hz hz0) coverPolynomial coverPolynomial
    (by rw [deck_polynomial])
@[simp] lemma deckRingEquiv_root (z : ℂ) (hz : z^6=1) (hz0 : z ≠ 0) :
    deckRingEquiv z hz hz0 (AdjoinRoot.root coverPolynomial)=AdjoinRoot.root coverPolynomial := by
  simp [deckRingEquiv]
@[simp] lemma deckRingEquiv_of (z : ℂ) (hz : z^6=1) (hz0 : z ≠ 0)
    (p : MvPolynomial (Fin 4) BaseField) :
    deckRingEquiv z hz hz0 (AdjoinRoot.of coverPolynomial p)=
      AdjoinRoot.of coverPolynomial (commonDeckCoefficientEquiv z hz hz0 p) := by
  simp [deckRingEquiv]
def deckFieldEquiv (z : ℂ) (hz : z^6=1) (hz0 : z ≠ 0) : CoverField ≃+* CoverField :=
  IsFractionRing.ringEquivOfRingEquiv (deckRingEquiv z hz hz0)
@[simp] lemma deckFieldEquiv_ring (z : ℂ) (hz : z^6=1) (hz0 : z ≠ 0) (r : CoverRing) :
    deckFieldEquiv z hz hz0 (algebraMap CoverRing CoverField r)=
      algebraMap CoverRing CoverField (deckRingEquiv z hz hz0 r) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap _ _
@[simp] lemma deckFieldEquiv_base (z : ℂ) (hz : z^6=1) (hz0 : z ≠ 0) (c : BaseField) :
    deckFieldEquiv z hz hz0 (algebraMap BaseField CoverField c)=
      algebraMap BaseField CoverField
        (genericBaseScaleEquiv z⁻¹ (by rw [inv_pow,hz,inv_one]) (inv_ne_zero hz0) c) := by
  rw [IsScalarTower.algebraMap_apply BaseField CoverRing CoverField,deckFieldEquiv_ring]
  change algebraMap CoverRing CoverField
    (deckRingEquiv z hz hz0 (AdjoinRoot.of _ (MvPolynomial.C c)))=_
  rw [deckRingEquiv_of,commonDeckCoefficientEquiv_C]
  rfl
@[simp] lemma deckFieldEquiv_complex (z : ℂ) (hz : z^6=1) (hz0 : z ≠ 0) (c : ℂ) :
    deckFieldEquiv z hz hz0 (algebraMap ℂ CoverField c)=algebraMap ℂ CoverField c := by
  rw [IsScalarTower.algebraMap_apply ℂ BaseField CoverField,deckFieldEquiv_base,
    genericBaseScaleEquiv_coefficient]
@[simp] lemma deckFieldEquiv_alpha (z : ℂ) (hz : z^6=1) (hz0 : z ≠ 0) :
    deckFieldEquiv z hz hz0 coverAlpha=algebraMap ℂ CoverField z⁻¹*coverAlpha := by
  rw [coverAlpha,deckFieldEquiv_base,alpha_eq,genericBaseScaleEquiv_alpha,map_mul,
    ← IsScalarTower.algebraMap_apply]
@[simp] lemma deckFieldEquiv_beta (z : ℂ) (hz : z^6=1) (hz0 : z ≠ 0) :
    deckFieldEquiv z hz hz0 coverBeta=algebraMap ℂ CoverField z⁻¹*coverBeta := by
  rw [coverBeta,deckFieldEquiv_base,beta_eq,genericBaseScaleEquiv_beta,map_mul,
    ← IsScalarTower.algebraMap_apply]
@[simp] lemma deckFieldEquiv_x0 (z : ℂ) (hz : z^6=1) (hz0 : z ≠ 0) :
    deckFieldEquiv z hz hz0 coverX0=coverX0 := by simp [coverX0]
@[simp] lemma deckFieldEquiv_parameter (z : ℂ) (hz : z^6=1) (hz0 : z ≠ 0) (i : Fin 4) :
    deckFieldEquiv z hz hz0 (coverCoefficientMap (MvPolynomial.X i))=
      ![coverX1,coverX2,coverY,algebraMap ℂ CoverField z*coverT] i := by
  simp only [coverCoefficientMap,RingHom.comp_apply,deckFieldEquiv_ring,
    deckRingEquiv_of,commonDeckCoefficientEquiv_X]
  fin_cases i
  · rfl
  · rfl
  · rfl
  · change algebraMap CoverRing CoverField (AdjoinRoot.of _
      (MvPolynomial.C (algebraMap ℂ BaseField z)*MvPolynomial.X 3))=_
    rw [map_mul,map_mul,cover_of_C,← IsScalarTower.algebraMap_apply ℂ BaseField CoverField]
    rfl
@[simp] lemma deckFieldEquiv_T (z : ℂ) (hz : z^6=1) (hz0 : z ≠ 0) :
    deckFieldEquiv z hz hz0 coverT=algebraMap ℂ CoverField z*coverT :=
  deckFieldEquiv_parameter z hz hz0 3
private lemma scaled_product_fixed (e : CoverField ≃+* CoverField)
    (z : ℂ) (hz : z ≠ 0) (a : CoverField)
    (ha : e a=algebraMap ℂ CoverField z⁻¹*a)
    (ht : e coverT=algebraMap ℂ CoverField z*coverT) : e (a*coverT)=a*coverT := by
  rw [map_mul,ha,ht]
  have hz' : algebraMap ℂ CoverField z⁻¹*algebraMap ℂ CoverField z=1 := by
    rw [← map_mul,inv_mul_cancel₀ hz,map_one]
  linear_combination a*coverT*hz'
@[simp] lemma deckFieldEquiv_Y0 (z : ℂ) (hz : z^6=1) (hz0 : z ≠ 0) :
    deckFieldEquiv z hz hz0 (coverAlpha*coverT)=coverAlpha*coverT :=
  scaled_product_fixed _ z hz0 _ (deckFieldEquiv_alpha z hz hz0) (deckFieldEquiv_T z hz hz0)
@[simp] lemma deckFieldEquiv_Y2 (z : ℂ) (hz : z^6=1) (hz0 : z ≠ 0) :
    deckFieldEquiv z hz hz0 (coverBeta*coverT)=coverBeta*coverT :=
  scaled_product_fixed _ z hz0 _ (deckFieldEquiv_beta z hz hz0) (deckFieldEquiv_T z hz hz0)
lemma deckFieldEquiv_fixes_residue (z : ℂ) (hz : z^6=1) (hz0 : z ≠ 0) (p : HodgeComputer.Poly) :
    deckFieldEquiv z hz hz0 (physicalFieldMap (physicalResidueMap p))=
      physicalFieldMap (physicalResidueMap p) := by
  have he : (deckFieldEquiv z hz hz0).toRingHom.comp (physicalFieldMap.comp physicalResidueMap)=
      physicalFieldMap.comp physicalResidueMap := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply,RingEquiv.coe_toRingHom,physicalResidueMap_C,
        physicalFieldMap_base]
      exact deckFieldEquiv_complex z hz hz0 c
    · intro i
      simp only [RingHom.comp_apply,RingEquiv.coe_toRingHom,physicalFieldMap_residue_X]
      fin_cases i <;> simp [coverX1,coverX2,coverY,deckFieldEquiv_parameter]
  exact RingHom.congr_fun he p
lemma deckFieldEquiv_fixes_physical (z : ℂ) (hz : z^6=1) (hz0 : z ≠ 0) (r : PhysicalField) :
    deckFieldEquiv z hz hz0 (physicalFieldMap r)=physicalFieldMap r := by
  have he : (deckFieldEquiv z hz hz0).toRingHom.comp physicalFieldMap=physicalFieldMap := by
    apply IsFractionRing.ringHom_ext (A := PhysicalRing)
    intro x
    obtain ⟨p,rfl⟩ := physicalProjection_surjective x
    exact deckFieldEquiv_fixes_residue z hz hz0 p
  exact RingHom.congr_fun he r
def physicalDeckAlgHom (z : ℂ) (hz : z^6=1) (hz0 : z ≠ 0) : CoverField →ₐ[PhysicalField] CoverField :=
  { (deckFieldEquiv z hz hz0).toRingHom with commutes' := deckFieldEquiv_fixes_physical z hz hz0 }
lemma cover_trace_inverse_fourth :
    Algebra.normalizedTrace PhysicalField CoverField ((coverT^4)⁻¹)=0 := by
  obtain ⟨z,hz,hz0,hz4⟩ := exists_nontrivial_sixth_root
  apply normalizedTrace_inv_fourth_zero (physicalDeckAlgHom z hz hz0)
    (algebraMap ℂ PhysicalField z) ?_ coverT ?_
  · intro h
    apply hz4
    apply (algebraMap ℂ PhysicalField).injective
    simpa only [map_pow,map_one] using h
  · change deckFieldEquiv z hz hz0 coverT=_
    rw [deckFieldEquiv_T,← IsScalarTower.algebraMap_apply]
end DeformedCover
#print axioms DeformedCover.deck_polynomial
#print axioms DeformedCover.deckFieldEquiv_fixes_physical
#print axioms DeformedCover.cover_trace_inverse_fourth
