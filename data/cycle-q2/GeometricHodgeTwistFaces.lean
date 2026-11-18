import Proposal.GeometricHodgeThreefold
import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization

/-!
# Standard intersections of the moving weighted projective threefold

An intersection containing the i-th chart is the projective basic open
of xᵢ times the product of its other inverted coordinates. Its section
ring is the actual degree-zero homogeneous localization. Relative to
the i-th chart it inverts the product of the normalized coordinates.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2HodgeTwistFaces
open AlgebraicGeometry CategoryTheory TopologicalSpace HomogeneousLocalization
open CycleQ2GeometricHodgeThreefold
open CycleQ2GenericSexticGradient (CoeffRing)

variable {R : Type} [CommRing R] (φ : CoeffRing →+* R) (i : Fin 4) (B : Finset (Fin 3))

abbrev faceVertex (q : Fin 3) : Fin 4 := i.succAbove q
abbrev product : cone φ := ∏ q ∈ B, coord φ (faceVertex i q).castSucc
abbrev anchorProduct : cone φ := coord φ i.castSucc * product φ i B

theorem product_mem : product φ i B ∈ grade φ B.card := by
  simpa using (SetLike.prod_mem_graded (grade φ) (fun _ : Fin 3 => 1)
    (fun q => coord φ (faceVertex i q).castSucc) (F := B)
    (fun q _ => weightOne_mem_grade φ (faceVertex i q)))

theorem anchorProduct_mem : anchorProduct φ i B ∈ grade φ (1+B.card) :=
  SetLike.mul_mem_graded (weightOne_mem_grade φ i) (product_mem φ i B)

def face : (threefold φ).Opens := Proj.basicOpen (grade φ) (anchorProduct φ i B)

theorem face_eq :
    face φ i B = coordinateOpen φ i ⊓ B.inf (fun q => coordinateOpen φ (faceVertex i q)) := by
  rw [face, anchorProduct, Proj.basicOpen_mul]
  congr 1
  induction B using Finset.induction_on with
  | empty => simp [product, Proj.basicOpen_one]
  | insert q B h ih =>
    simpa [product, Finset.prod_insert h, Finset.inf_insert, Proj.basicOpen_mul, coordinateOpen] using
      congrArg (fun W => coordinateOpen φ (faceVertex i q) ⊓ W) ih

/-- Every standard intersection containing its anchor is one of these faces. -/
theorem face_inf (S : Finset (Fin 4)) (hi : i ∈ S) :
    face φ i (Finset.univ.filter (fun q => faceVertex i q ∈ S)) = S.inf (coordinateOpen φ) := by
  rw [face_eq]
  apply le_antisymm
  · apply Finset.le_inf
    intro j hj
    by_cases he : j = i
    · subst j; exact inf_le_left
    · obtain ⟨q,rfl⟩ := Fin.exists_succAbove_eq he
      exact inf_le_right.trans (Finset.inf_le (by simpa [faceVertex] using hj))
  · exact le_inf (Finset.inf_le hi) (Finset.le_inf fun q hq =>
      Finset.inf_le (Finset.mem_filter.mp hq).2)

theorem face_affine : IsAffineOpen (face φ i B) :=
  Proj.isAffineOpen_basicOpen (grade φ) (anchorProduct φ i B) (anchorProduct_mem φ i B) (by omega)

abbrev FaceRing := Away (grade φ) (anchorProduct φ i B)

def sectionsEquiv : FaceRing φ i B ≃+* Γ(threefold φ, face φ i B) :=
  (Proj.basicOpenIsoAway (grade φ) (anchorProduct φ i B) (anchorProduct_mem φ i B) (by omega)).commRingCatIsoToRingEquiv

def denominator : ChartRing φ i :=
  Away.isLocalizationElem (weightOne_mem_grade φ i) (product_mem φ i B)

def toFace : ChartRing φ i →+* FaceRing φ i B := awayMap (grade φ) (product_mem φ i B) rfl

theorem face_localization :
    letI := (toFace φ i B).toAlgebra
    IsLocalization.Away (denominator φ i B) (FaceRing φ i B) :=
  Away.isLocalization_mul (weightOne_mem_grade φ i) (product_mem φ i B) rfl (by decide)

set_option maxHeartbeats 600000 in
/-- Every further standard intersection restricts the original Proj fraction. -/
theorem toFace_section (p : ChartRing φ i) :
    sectionsEquiv φ i B (toFace φ i B p) =
      (threefold φ).presheaf.map (homOfLE (show face φ i B ≤ coordinateOpen φ i by
        rw [face_eq]; exact inf_le_left)).op (Proj.awayToSection (grade φ) (coord φ i.castSucc) p) := by
  change (Proj.awayToSection (grade φ) (anchorProduct φ i B)) (toFace φ i B p) = _
  have h := Proj.awayMap_awayToSection (grade φ) (product_mem φ i B)
    (show anchorProduct φ i B = coord φ i.castSucc * product φ i B from rfl)
  have he := congrArg (fun u : CommRingCat.of (ChartRing φ i) ⟶ Γ(threefold φ,face φ i B) => u.hom p) h
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at he
  exact he

end CycleQ2HodgeTwistFaces
end

#print axioms CycleQ2HodgeTwistFaces.face_localization
#print axioms CycleQ2HodgeTwistFaces.toFace_section
