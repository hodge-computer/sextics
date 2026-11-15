import Proposal.GeometricSeedOverlapTransitionModels

/-!
# The actual matrix-image embeddings on the overlap models

An injective module map induces an injective map on every section module
of its associated sheaf: the proof uses injectivity after localization at
each prime. Applying this to the actual range-submodule inclusion embeds
the seed image sheaf into the associated rank-three module sheaf.

The overlap image transition intertwines these literal embeddings with
multiplication by the positive fourteenth power of the coordinate ratio.
The original matrix still factors through the same range inclusion.
Identification with a common global free sheaf and triple-overlap descent
are subsequent steps.

Source-only draft: no Lean elaboration or kernel replay has been run.
Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md for
attribution of the geometric route and the protected certificate gap.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

namespace CycleQ2SeedImageSheafEmbedding

open CategoryTheory AlgebraicGeometry
open CycleQ2SegreFactorSequence CycleQ2SeedProjectiveImageTwist

section Tilde

variable {R : CommRingCat.{u}} {M N : ModuleCat.{u} R}

/-- Injectivity of a module map survives on every associated-sheaf section. -/
theorem tilde_map_app_injective (f : M ⟶ N) (hf : Function.Injective f.hom)
    (U : (Spec R).Opens) : Function.Injective ((tilde.map f).app U) := by
  intro s t hst
  apply Subtype.ext
  funext x
  apply IsLocalizedModule.map_injective x.1.asIdeal.primeCompl
    (LocalizedModule.mkLinearMap x.1.asIdeal.primeCompl M)
    (LocalizedModule.mkLinearMap x.1.asIdeal.primeCompl N) f.hom hf
  exact congrArg (fun z : Γ(tilde N, U) => z.1 x) hst

/-- This monomorphism proof uses componentwise injectivity directly. -/
theorem tilde_map_mono (f : M ⟶ N) (hf : Function.Injective f.hom) :
    Mono (tilde.map f) where
  right_cancellation {P} g h H := by
    apply Scheme.Modules.hom_ext
    intro U
    apply ConcreteCategory.hom_ext
    intro s
    apply tilde_map_app_injective f hf U
    exact congrArg (fun k : P ⟶ tilde N => k.app U s) H

end Tilde

section Image

variable {R : Type u} [CommRing R]

abbrev rankThreeSheaf (R : Type u) [CommRing R] :=
  tilde (R := CommRingCat.of R) (ModuleCat.of R (Fin 3 → R))

/-- The inclusion is the literal subtype map of the original matrix range. -/
def imageInclusion (F : FactorData R) :
    ModuleCat.of R (Regrading.Image F) ⟶ ModuleCat.of R (Fin 3 → R) :=
  ModuleCat.ofHom (Regrading.Image F).subtype

/-- The original matrix, with only its codomain restricted to its range. -/
def matrixToImage (F : FactorData R) :
    ModuleCat.of R (Fin 3 → R) ⟶ ModuleCat.of R (Regrading.Image F) :=
  ModuleCat.ofHom F.matrix.mulVecLin.rangeRestrict

theorem matrixToImage_inclusion (F : FactorData R) :
    matrixToImage F ≫ imageInclusion F = ModuleCat.ofHom F.matrix.mulVecLin := rfl

/-- Associated-sheaf embedding of the actual matrix-image module. -/
def imageEmbedding (F : FactorData R) :
    tilde (R := CommRingCat.of R) (ModuleCat.of R (Regrading.Image F)) ⟶
      rankThreeSheaf R :=
  tilde.map (imageInclusion F)

theorem imageEmbedding_app_injective (F : FactorData R)
    (U : (Spec (CommRingCat.of R)).Opens) :
    Function.Injective ((imageEmbedding F).app U) :=
  tilde_map_app_injective (imageInclusion F) Subtype.val_injective U

instance imageEmbedding_mono (F : FactorData R) : Mono (imageEmbedding F) :=
  tilde_map_mono (imageInclusion F) Subtype.val_injective

theorem matrixToImage_embedding (F : FactorData R) :
    tilde.map (matrixToImage F) ≫ imageEmbedding F =
      tilde.map (ModuleCat.ofHom F.matrix.mulVecLin) := by
  rw [imageEmbedding, ← tilde.map_comp, matrixToImage_inclusion]

/-- The ambient scalar map retains the prescribed degree fourteen. -/
def scalar14Map (t : Rˣ) :
    ModuleCat.of R (Fin 3 → R) ⟶ ModuleCat.of R (Fin 3 → R) :=
  ModuleCat.ofHom ((t : R) ^ 14 • (LinearMap.id : (Fin 3 → R) →ₗ[R] (Fin 3 → R)))

def scalar14SheafMap (t : Rˣ) : rankThreeSheaf R ⟶ rankThreeSheaf R :=
  tilde.map (scalar14Map t)

theorem imageTransition_inclusion (F G : FactorData R) (t : Rˣ)
    (hM : G.matrix = (t : R) ^ 14 • F.matrix) :
    (CycleQ2SeedImageTwistedDuality.imageTransition F G t hM).toModuleIso.hom ≫
        imageInclusion G = imageInclusion F ≫ scalar14Map t := by
  apply ModuleCat.hom_ext
  exact LinearMap.ext
    (CycleQ2SeedImageTwistedDuality.imageTransition_val F G t hM)

/-- Applying the associated-sheaf functor preserves the literal inclusion square. -/
theorem imageTransition_embedding (F G : FactorData R) (t : Rˣ)
    (hM : G.matrix = (t : R) ^ 14 • F.matrix) :
    tilde.map
        (CycleQ2SeedImageTwistedDuality.imageTransition F G t hM).toModuleIso.hom ≫
        imageEmbedding G = imageEmbedding F ≫ scalar14SheafMap t := by
  rw [imageEmbedding, imageEmbedding, scalar14SheafMap,
    ← tilde.map_comp, ← tilde.map_comp, imageTransition_inclusion]

end Image

section ActualOverlap

open CycleQ2SeedProjectiveImageRestriction CycleQ2SeedProjectiveImageCompatibility
  CycleQ2SeedProjectiveLocalizedDuality CycleQ2SeedOverlapTransitionModels

def leftModelEmbedding (i j : Fin 3) :
    leftImageModelSheaf i j ⟶ rankThreeSheaf (OverlapSections i j) :=
  imageEmbedding (leftData i j)

def rightModelEmbedding (i j : Fin 3) :
    rightImageModelSheaf i j ⟶ rankThreeSheaf (OverlapSections i j) :=
  imageEmbedding (rightData i j)

instance leftModelEmbedding_mono (i j : Fin 3) : Mono (leftModelEmbedding i j) :=
  imageEmbedding_mono (leftData i j)

instance rightModelEmbedding_mono (i j : Fin 3) : Mono (rightModelEmbedding i j) :=
  imageEmbedding_mono (rightData i j)

/-- The actual pair-overlap transition satisfies the prescribed ambient square. -/
theorem overlapModel_embedding (i j : Fin 3) :
    (modelImageTransition i j).hom ≫ rightModelEmbedding i j =
      leftModelEmbedding i j ≫ scalar14SheafMap (ratioUnit i j) :=
  imageTransition_embedding (leftData i j) (rightData i j) (ratioUnit i j)
    (data_matrix_change i j)

#print axioms tilde_map_app_injective
#print axioms tilde_map_mono
#print axioms matrixToImage_embedding
#print axioms imageEmbedding_mono
#print axioms overlapModel_embedding

end ActualOverlap

end CycleQ2SeedImageSheafEmbedding
end
