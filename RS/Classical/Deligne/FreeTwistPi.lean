import RS.Classical.Deligne.GammaPair
import RS.Classical.Deligne.TwistFreeTensor

/-!
# The free factor on the projection

The relative tensor of a free module with a module is the twist of
that module by the generating object, `RS.freeTensorTwistIso`.
This file computes that comparison on the canonical projection: it
carries the algebra past the generator, reassociates, and acts.

* `modTensorπ_freeTensorTwistIso`: the projection formula.
* `freeTensorTwistIso_gpair`: the same statement for the pairing
  `RS.gpair`, which is the form the comparison map of the Γ-modules
  consumes.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  [SymmetricCategory D]
variable [Preadditive D] [MonoidalPreadditive D]
  [HasCoequalizers D]
variable [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair
  (tensorLeft Z)]
variable [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair
  (tensorRight Z)]
variable (A : D) [MonObj A] [IsCommMonObj A]

omit [Preadditive D] [MonoidalPreadditive D] [HasCoequalizers D]
  [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair
    (tensorLeft Z)]
  [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair
    (tensorRight Z)]
  [MonObj A] [IsCommMonObj A] in
/-- The coherence behind the projection formula: crossing the
generator, interchanging against the unit factor and collapsing
the resulting right unitor is the crossing followed by the
reassociation.  The interchange meets the tensor unit, so its
braiding is a pair of unitors. -/
theorem freeTwistInterchange (V X : D) :
    ((β_ A V).hom ⊗ₘ (λ_ X).inv) ≫ tensorμ V A (𝟙_ D) X ≫
        ((ρ_ V).hom ▷ (A ⊗ X)) =
      ((β_ A V).hom ▷ X) ≫ (α_ V A X).hom := by
  rw [tensorμ, braiding_tensorUnit_right]
  simp only [tensorHom_def, Category.assoc]
  monoidal

variable (V : D) (M : Mod D A)

omit [Preadditive D] [MonoidalPreadditive D]
  [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair
    (tensorRight Z)] in
/-- **The free factor on the projection**: the isomorphism
identifying the relative tensor of a free module with the twist of
the module carries the projection to the crossing of the algebra
past the generator, followed by the action. -/
theorem modTensorπ_freeTensorTwistIso :
    modTensorπ A (freeMod A V) M ≫
        (freeTensorTwistIso A V M).hom.hom =
      ((β_ A V).hom ▷ M.X) ≫ (α_ V A M.X).hom ≫
        (V ◁ actLeft A M.X) := by
  have hπ : modTensorπ A (regularMod A) M ≫
      (modTensorUnitLeft A M).hom = actLeft A M.X :=
    modTensorπ_desc A (regularMod A) M _ _
  show modTensorπ A (freeMod A V) M ≫
      modTensorMap A (freeRegTwistIso A V).hom
          (tensorLeftUnitMod A M).symm.hom ≫
        twistShuffleHom A V (𝟙_ D) (regularMod A) M ≫
        ((ρ_ V).hom ▷ modTensor A (regularMod A) M) ≫
        (V ◁ (modTensorUnitLeft A M).hom) =
    ((β_ A V).hom ▷ M.X) ≫ (α_ V A M.X).hom ≫
      (V ◁ actLeft A M.X)
  rw [modTensorπ_map_assoc, modTensorπ_twistShuffleHom_assoc]
  show ((β_ A V).hom ⊗ₘ (λ_ M.X).inv) ≫
      (tensorμ V A (𝟙_ D) M.X ≫
        ((V ⊗ 𝟙_ D) ◁ modTensorπ A (regularMod A) M)) ≫
      ((ρ_ V).hom ▷ modTensor A (regularMod A) M) ≫
      (V ◁ (modTensorUnitLeft A M).hom) =
    ((β_ A V).hom ▷ M.X) ≫ (α_ V A M.X).hom ≫
      (V ◁ actLeft A M.X)
  simp only [Category.assoc]
  rw [whisker_exchange_assoc, ← MonoidalCategory.whiskerLeft_comp,
    hπ, reassoc_of% freeTwistInterchange A V M.X]

omit [Preadditive D] [MonoidalPreadditive D]
  [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair
    (tensorRight Z)] in
/-- **The free factor on the pairing**: the pairing `RS.gpair` of a
morphism into a free module with a morphism into a module is, after
the identification of the relative tensor with the twist, the
tensor of the two morphisms followed by the crossing and the
action. -/
theorem freeTensorTwistIso_gpair {X Y : D} (m : X ⟶ A ⊗ V)
    (n : Y ⟶ M.X) :
    gpair (M := freeMod A V) (N := M) m n ≫
        (freeTensorTwistIso A V M).hom.hom =
      (m ⊗ₘ n) ≫ ((β_ A V).hom ▷ M.X) ≫ (α_ V A M.X).hom ≫
        (V ◁ actLeft A M.X) := by
  rw [gpair_def, Category.assoc]
  exact whisker_eq _ (modTensorπ_freeTensorTwistIso A V M)

end RS
