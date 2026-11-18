import Proposal.GeometricHodgeTwistDehom
import Proposal.GeometricSurfaceCoordinates

/-!
# Localized coefficients of the moving cubic

Choose one of the inverted weight-one coordinates as origin of the chart.
The other inverted coordinates generate a single product denominator.
Clearing its powers identifies the coefficient ring with the Laurent
polynomials supported on precisely the allowed integer exponents.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2HodgeTwistLocalization
open CycleQ2HodgeTwistCech CycleQ2HodgeTwistDehom
open CycleQ2SeedCechThreeOpen CycleQ2SeedCechLocalization

def inverted (i : Vertex) (S : Finset Vertex) : Finset (Fin 3) :=
  Finset.univ.filter fun q => i.succAbove q ∈ S

@[simp] theorem mem_inverted (i : Vertex) (S : Finset Vertex) (q : Fin 3) :
    q ∈ inverted i S ↔ i.succAbove q ∈ S := by simp [inverted]

variable (R : Type*) [CommRing R] (i : Vertex) (S : Finset Vertex)

private def coeffMap : coordinateLocalization R (inverted i S) →+ (Offset i S →₀ R) where
  toFun x := ((localizationToLaurent R _ x).coeff).subtypeDomain _
  map_zero' := by ext e; change (localizationToLaurent R _ 0).coeff e.val = 0; rw [map_zero]; rfl
  map_add' x y := by
    ext e
    change (localizationToLaurent R _ (x+y)).coeff e.val = _ + _
    rw [map_add]
    rfl

theorem coeffMap_injective : Function.Injective (coeffMap R i S) := by
  intro x y h
  apply localizationToLaurent_injective R (inverted i S)
  apply AddMonoidAlgebra.coeff_injective
  ext e
  by_cases he : ∀ q, e q < 0 → i.succAbove q ∈ S
  · exact DFunLike.congr_fun h ⟨e, he⟩
  · push Not at he
    obtain ⟨q,hq,hout⟩ := he
    have h' : q ∉ inverted i S := fun z => hout ((mem_inverted i S q).mp z)
    rw [localizationToLaurent_hasPoles R _ x e q h' hq, localizationToLaurent_hasPoles R _ y e q h' hq]

theorem coeffMap_surjective : Function.Surjective (coeffMap R i S) := by
  classical
  intro v
  let p : Laurent (R := R) := AddMonoidAlgebra.ofCoeff v.extendDomain
  have hp : HasPoles (inverted i S) p := by
    intro e q hq he
    change v.extendDomain e = 0
    have hn : ¬ (∀ a, e a < 0 → i.succAbove a ∈ S) :=
      fun h => hq ((mem_inverted i S q).mpr (h q he))
    rw [Finsupp.extendDomain_apply, dif_neg hn]
  obtain ⟨x,hx⟩ := (mem_range_localizationToLaurent R _ p).mpr hp
  refine ⟨x, ?_⟩
  change (localizationToLaurent R _ x).coeff.subtypeDomain _ = v
  rw [hx]
  exact Finsupp.subtypeDomain_extendDomain v

/-- The Laurent coefficients of the literal product localization of the chart base. -/
def localizationOffset : coordinateLocalization R (inverted i S) ≃+ (Offset i S →₀ R) :=
  AddEquiv.ofBijective (coeffMap R i S) ⟨coeffMap_injective R i S, coeffMap_surjective R i S⟩

@[simp] theorem localizationOffset_coeff (x : coordinateLocalization R (inverted i S)) (b : Offset i S) :
    localizationOffset R i S x b = (localizationToLaurent R _ x).coeff b.val := rfl

/-- The full Laurent face consists of three genuine localized polynomial coefficients. -/
def intersectionCoordinates (t : ℤ) (hi : i ∈ S) :
    sections R t S ≃+ (Fin 3 → coordinateLocalization R (inverted i S)) :=
  (chartCoordinates t i S hi).trans (AddEquiv.piCongrRight fun _ => (localizationOffset R i S).symm)

/-- Summation over normalized chart exponents is summation of the same finite coefficients
over the homogeneous rows. -/
theorem sum_intersection {G : Type*} [AddCommMonoid G] (t : ℤ) (hi : i ∈ S)
    (p : sections R t S) (j : Fin 3) (g : (Fin 3 → ℤ) → R → G) :
    (localizationToLaurent R _ (intersectionCoordinates R i S t hi p j)).coeff.sum g =
      (p.val j).sum (fun e c => g (fun q => e (i.succAbove q)) c) := by
  classical
  let x := intersectionCoordinates R i S t hi p j
  let L := localizationToLaurent R (inverted i S) x
  let P := fun b : Fin 3 → ℤ => ∀ q, b q < 0 → i.succAbove q ∈ S
  have hs (b) (hb : b ∈ L.coeff.support) : P b := by
    intro q hq
    by_contra hout
    exact (Finsupp.mem_support_iff.mp hb) (localizationToLaurent_hasPoles R _ x b q
      (fun h => hout ((mem_inverted i S q).mp h)) hq)
  have hraw (e) (he : e ∈ (p.val j).support) : Allowed t S j e := by
    by_contra hbad
    exact (Finsupp.mem_support_iff.mp he) (p.property j e hbad)
  have hx : L.coeff.subtypeDomain P = chartCoordinates t i S hi p j := by
    exact (localizationOffset R i S).apply_symm_apply _
  calc
    _ = (L.coeff.subtypeDomain P).sum (fun b c => g b.val c) := (Finsupp.sum_subtypeDomain_index hs).symm
    _ = (chartCoordinates t i S hi p j).sum (fun b c => g b.val c) := by rw [hx]
    _ = ((p.val j).subtypeDomain (Allowed t S j)).sum
        (fun e c => g (fun q => e.val (i.succAbove q)) c) :=
      Finsupp.sum_equivMapDomain (exponentEquiv t j i S hi) _ _
    _ = _ := Finsupp.sum_subtypeDomain_index (h := fun e c => g (fun q => e (i.succAbove q)) c) hraw

end CycleQ2HodgeTwistLocalization
end

#print axioms CycleQ2HodgeTwistLocalization.intersectionCoordinates
