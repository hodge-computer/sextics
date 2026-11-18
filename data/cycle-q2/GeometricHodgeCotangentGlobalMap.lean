import Proposal.GeometricHodgeCotangentAtlasForms

/-!
# Gluing the actual cotangent Euler map

The local differential formulas agree on every pair intersection and
commute with restriction. The ordinary sheaf gluing axiom therefore gives
one morphism from the actual negative-twist Euler kernel to the original
sheaf of complex differentials. Its restriction to every chart subopen
is the original coordinate formula.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 3000
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeCotangentGlobalMap

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open CycleQ2GeometricHodgeThreefold
open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2HodgeTwistRatios (U)
open CycleQ2HodgeCotangentEulerSheaf (ambient)
open CycleQ2HodgeCotangentAtlasForms (Cotangent localForm localForm_change
  localForm_restrict localForm_add localForm_smul)
open CycleQ2SeedSectionSheafLocal (moduleRes moduleRes_comp)
open CycleQ2GeometricModuleLocalIso (addSheaf)

variable (φ : CoeffRing →+* ℂ) (h : IsUnit (φ vertexCoefficient))

include h in
private theorem chart_cover (V : (threefold φ).Opens) :
    (⨆ i : Fin 4, V ⊓ U φ i) = V := by
  rw [← inf_iSup_eq,coordinateOpens_cover φ h,inf_top_eq]

include h in
private theorem section_ext (V : (threefold φ).Opens) (s t : Γ(Cotangent φ,V))
    (hs : ∀ i : Fin 4, moduleRes (Cotangent φ) (show V ⊓ U φ i ≤ V from inf_le_left) s =
      moduleRes (Cotangent φ) inf_le_left t) : s = t :=
  (addSheaf (Cotangent φ)).eq_of_locally_eq' (fun i : Fin 4 => V ⊓ U φ i) V
    (fun _ => homOfLE inf_le_left) (chart_cover φ h V).ge s t hs

include h in
private theorem exists_globalForm (V : (threefold φ).Opens) (a : Γ(ambient φ,V)) :
    ∃ s : Γ(Cotangent φ,V), ∀ i : Fin 4,
      moduleRes (Cotangent φ) (show V ⊓ U φ i ≤ V from inf_le_left) s =
        localForm φ i (V ⊓ U φ i) inf_le_right (moduleRes (ambient φ) inf_le_left a) := by
  let VU : Fin 4 → (threefold φ).Opens := fun i => V ⊓ U φ i
  let sf : ∀ i : Fin 4, Γ(Cotangent φ,VU i) :=
    fun i => localForm φ i (VU i) inf_le_right (moduleRes (ambient φ) inf_le_left a)
  have hc : TopCat.Presheaf.IsCompatible (addSheaf (Cotangent φ)).obj VU sf := by
    intro i j
    change moduleRes (Cotangent φ) (inf_le_left : VU i ⊓ VU j ≤ VU i) (sf i) =
      moduleRes (Cotangent φ) inf_le_right (sf j)
    rw [localForm_restrict,localForm_restrict,moduleRes_comp,moduleRes_comp]
    exact localForm_change φ i j (VU i ⊓ VU j) _ _ _
  obtain ⟨s,hs,_⟩ := (addSheaf (Cotangent φ)).existsUnique_gluing' VU V
    (fun _ => homOfLE inf_le_left) (chart_cover φ h V).ge sf hc
  exact ⟨s,hs⟩

def globalForm (V : (threefold φ).Opens) (a : Γ(ambient φ,V)) : Γ(Cotangent φ,V) :=
  Classical.choose (exists_globalForm φ h V a)

theorem globalForm_restrict_chart (V : (threefold φ).Opens) (a : Γ(ambient φ,V)) (i : Fin 4) :
    moduleRes (Cotangent φ) (show V ⊓ U φ i ≤ V from inf_le_left) (globalForm φ h V a) =
      localForm φ i (V ⊓ U φ i) inf_le_right (moduleRes (ambient φ) inf_le_left a) :=
  Classical.choose_spec (exists_globalForm φ h V a) i

/-- The glued map is the coordinate formula on every subopen, not just on vertices. -/
theorem globalForm_on_subopen (i : Fin 4) {V W : (threefold φ).Opens}
    (hWV : W ≤ V) (hi : W ≤ U φ i) (a : Γ(ambient φ,V)) :
    moduleRes (Cotangent φ) hWV (globalForm φ h V a) =
      localForm φ i W hi (moduleRes (ambient φ) hWV a) := by
  calc
    _ = moduleRes (Cotangent φ) (le_inf hWV hi)
        (moduleRes (Cotangent φ) (inf_le_left : V ⊓ U φ i ≤ V) (globalForm φ h V a)) :=
      (moduleRes_comp (Cotangent φ) inf_le_left (le_inf hWV hi) _).symm
    _ = moduleRes (Cotangent φ) (le_inf hWV hi)
        (localForm φ i (V ⊓ U φ i) inf_le_right (moduleRes (ambient φ) inf_le_left a)) := by
      rw [globalForm_restrict_chart]
    _ = localForm φ i W hi (moduleRes (ambient φ) (le_inf hWV hi)
        (moduleRes (ambient φ) inf_le_left a)) := localForm_restrict φ i inf_le_right _ _
    _ = _ := congrArg (localForm φ i W hi) (moduleRes_comp (ambient φ) inf_le_left (le_inf hWV hi) a)

private theorem res_smul {X : Scheme.{0}} (M : X.Modules) {V W : X.Opens} (hWV : W ≤ V)
    (c : Γ(X,V)) (a : Γ(M,V)) :
    moduleRes M hWV (c • a) = X.presheaf.map (homOfLE hWV).op c • moduleRes M hWV a :=
  M.val.map_smul (homOfLE hWV).op c a

theorem globalForm_add (V : (threefold φ).Opens) (a b : Γ(ambient φ,V)) :
    globalForm φ h V (a+b) = globalForm φ h V a + globalForm φ h V b := by
  apply section_ext φ h V
  intro i
  rw [map_add,globalForm_restrict_chart,globalForm_restrict_chart,globalForm_restrict_chart,
    map_add,localForm_add]

theorem globalForm_smul (V : (threefold φ).Opens) (c : Γ(threefold φ,V)) (a : Γ(ambient φ,V)) :
    globalForm φ h V (c • a) = c • globalForm φ h V a := by
  apply section_ext φ h V
  intro i
  rw [res_smul,globalForm_restrict_chart,globalForm_restrict_chart,res_smul,localForm_smul]

theorem globalForm_restrict {V W : (threefold φ).Opens} (hWV : W ≤ V) (a : Γ(ambient φ,V)) :
    moduleRes (Cotangent φ) hWV (globalForm φ h V a) =
      globalForm φ h W (moduleRes (ambient φ) hWV a) := by
  apply section_ext φ h W
  intro i
  rw [moduleRes_comp]
  rw [globalForm_on_subopen φ h i (inf_le_left.trans hWV) inf_le_right,
    globalForm_restrict_chart,moduleRes_comp]

def globalLinear (V : (threefold φ).Opens) :
    Γ(ambient φ,V) →ₗ[Γ(threefold φ,V)] Γ(Cotangent φ,V) where
  toFun := globalForm φ h V
  map_add' := globalForm_add φ h V
  map_smul' := globalForm_smul φ h V

def additiveGlobal : addSheaf (ambient φ) ⟶ addSheaf (Cotangent φ) where
  hom.app O := AddCommGrpCat.ofHom (globalLinear φ h O.unop).toAddMonoidHom
  hom.naturality {O P} f := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro a
    exact (globalForm_restrict φ h (leOfHom f.unop) a).symm

/-- A genuine morphism into the original sheafified Kähler differentials. -/
def toCotangent : ambient φ ⟶ Cotangent φ where
  val := PresheafOfModules.homMk (additiveGlobal φ h).hom
    (fun O c a => globalForm_smul φ h O.unop c a)

theorem toCotangent_on_subopen (i : Fin 4) (V : (threefold φ).Opens) (hi : V ≤ U φ i)
    (a : Γ(ambient φ,V)) : (toCotangent φ h).app V a = localForm φ i V hi a := by
  have he := globalForm_on_subopen φ h i (V := V) le_rfl hi a
  rw [CycleQ2SeedSectionSheafLocal.moduleRes_refl,CycleQ2SeedSectionSheafLocal.moduleRes_refl] at he
  exact he

end CycleQ2HodgeCotangentGlobalMap
end

#print axioms CycleQ2HodgeCotangentGlobalMap.globalForm_on_subopen
#print axioms CycleQ2HodgeCotangentGlobalMap.toCotangent
#print axioms CycleQ2HodgeCotangentGlobalMap.toCotangent_on_subopen
