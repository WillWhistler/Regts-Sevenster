import RS.Classical.Deligne.InterchangeAct

/-!
# The tensor product of duality data

Deligne's 1.15 tensor part: dual pairs tensor.  The pairing of
the tensor datum crosses the middle factors through the descended
interchange and pairs coordinatewise into the regular module; the
copairing unfolds the unit and inserts both copairings.  The
descended interchange exists because the interchange is linear in
both factors.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  [SymmetricCategory D]
variable [HasCoequalizers D]
variable [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair
  (tensorLeft Z)]
variable [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair
  (tensorRight Z)]
variable (A : D) [MonObj A] [IsCommMonObj A]

section InterchangeDesc

variable (X₁ X₂ Y₁ Y₂ : Mod D A)

/-- **The descended interchange**: the interchange of module
tensor products descends to the relative tensor of the bundles,
because it is linear in both factors. -/
noncomputable def interchangeDesc :
    modTensor A (modTensorMod A X₁ X₂) (modTensorMod A Y₁ Y₂) ⟶
      modTensor A (modTensorMod A X₁ Y₁) (modTensorMod A X₂ Y₂) :=
  modTensorDesc A (modTensorMod A X₁ X₂) (modTensorMod A Y₁ Y₂)
    (interchange A X₁ X₂ Y₁ Y₂)
    (by
      rw [modTensorLegM, modTensorLegN, actRight]
      show ((β_ (modTensor A X₁ X₂) A).hom ≫
          modTensorAct A X₁ X₂) ▷ modTensor A Y₁ Y₂ ≫
          interchange A X₁ X₂ Y₁ Y₂ =
        ((α_ (modTensor A X₁ X₂) A (modTensor A Y₁ Y₂)).hom ≫
          modTensor A X₁ X₂ ◁ modTensorAct A Y₁ Y₂) ≫
          interchange A X₁ X₂ Y₁ Y₂
      rw [comp_whiskerRight, Category.assoc,
        interchange_actLeft A X₁ X₂ Y₁ Y₂, Category.assoc,
        interchange_actMid A X₁ X₂ Y₁ Y₂,
        Iso.hom_inv_id_assoc])

/-- Defining equation of the descended interchange. -/
@[reassoc (attr := simp)]
theorem modTensorπ_interchangeDesc :
    modTensorπ A (modTensorMod A X₁ X₂) (modTensorMod A Y₁ Y₂) ≫
        interchangeDesc A X₁ X₂ Y₁ Y₂ =
      interchange A X₁ X₂ Y₁ Y₂ :=
  modTensorπ_desc A _ _ _ _

/-- The descended interchange intertwines the actions. -/
@[reassoc]
theorem interchangeDesc_act :
    modTensorAct A (modTensorMod A X₁ X₂) (modTensorMod A Y₁ Y₂) ≫
        interchangeDesc A X₁ X₂ Y₁ Y₂ =
      (A ◁ interchangeDesc A X₁ X₂ Y₁ Y₂) ≫
        modTensorAct A (modTensorMod A X₁ Y₁)
          (modTensorMod A X₂ Y₂) := by
  apply modTensor_whisker_hom_ext A (modTensorMod A X₁ X₂)
    (modTensorMod A Y₁ Y₂) A
  conv_lhs => rw [whiskerLeft_modTensorπ_act_assoc,
    modTensorπ_interchangeDesc]
  conv_rhs => rw [← MonoidalCategory.whiskerLeft_comp_assoc,
    modTensorπ_interchangeDesc]
  show (α_ A (modTensor A X₁ X₂) (modTensor A Y₁ Y₂)).inv ≫
      (modTensorAct A X₁ X₂ ▷ modTensor A Y₁ Y₂) ≫
      interchange A X₁ X₂ Y₁ Y₂ =
    (A ◁ interchange A X₁ X₂ Y₁ Y₂) ≫
      modTensorAct A (modTensorMod A X₁ Y₁)
        (modTensorMod A X₂ Y₂)
  rw [interchange_actLeft A X₁ X₂ Y₁ Y₂,
    Iso.inv_hom_id_assoc]

end InterchangeDesc

section Datum

variable {N₁ N₂ N₁' N₂' : Mod D A}

/-- The fold of the doubled regular module onto the base. -/
noncomputable def regPairFold :
    modTensor A (regularMod A) (regularMod A) ⟶ A :=
  (modTensorUnitLeft A (regularMod A)).hom

/-- **The tensor pairing**: cross through the descended
interchange, pair coordinatewise, and fold. -/
noncomputable def tensorPair (d₁ : ModDualityDatum A N₁ N₁')
    (d₂ : ModDualityDatum A N₂ N₂') :
    modTensor A (modTensorMod A N₁' N₂') (modTensorMod A N₁ N₂)
      ⟶ A :=
  interchangeDesc A N₁' N₂' N₁ N₂ ≫
    modTensorMap A d₁.pairMod d₂.pairMod ≫ regPairFold A

/-- The unfolding of the base into the doubled regular module. -/
noncomputable def regPairUnfold :
    A ⟶ modTensor A (regularMod A) (regularMod A) :=
  (modTensorUnitLeft A (regularMod A)).inv

/-- **The tensor copairing**: unfold the unit, insert both
copairings, and regroup through the descended interchange. -/
noncomputable def tensorCopair (d₁ : ModDualityDatum A N₁ N₁')
    (d₂ : ModDualityDatum A N₂ N₂') :
    A ⟶ modTensor A (modTensorMod A N₁ N₂)
      (modTensorMod A N₁' N₂') :=
  regPairUnfold A ≫
    modTensorMap A d₁.copairMod d₂.copairMod ≫
    interchangeDesc A N₁ N₁' N₂ N₂'

omit [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair
  (tensorRight Z)] in
/-- The inverse of the doubled-unit fold intertwines the
multiplication and the action. -/
theorem regPairUnfold_act :
    μ[A] ≫ regPairUnfold A =
      (A ◁ regPairUnfold A) ≫
        modTensorAct A (regularMod A) (regularMod A) := by
  rw [regPairUnfold, Iso.comp_inv_eq, Category.assoc,
    modTensorUnitLeft_hom_actLeft, ← Category.assoc,
    ← MonoidalCategory.whiskerLeft_comp, Iso.inv_hom_id,
    MonoidalCategory.whiskerLeft_id, Category.id_comp]
  rfl

/-- **The tensor pairing is linear.** -/
theorem tensorPair_linear (d₁ : ModDualityDatum A N₁ N₁')
    (d₂ : ModDualityDatum A N₂ N₂') :
    modTensorAct A (modTensorMod A N₁' N₂')
        (modTensorMod A N₁ N₂) ≫ tensorPair A d₁ d₂ =
      (A ◁ tensorPair A d₁ d₂) ≫ μ[A] := by
  rw [tensorPair, ← Category.assoc, interchangeDesc_act,
    Category.assoc,
    reassoc_of% (modTensorAct_map A d₁.pairMod d₂.pairMod),
    regPairFold, modTensorUnitLeft_hom_actLeft,
    ← MonoidalCategory.whiskerLeft_comp_assoc,
    ← MonoidalCategory.whiskerLeft_comp_assoc,
    Category.assoc]
  rfl

/-- **The tensor copairing is linear.** -/
theorem tensorCopair_linear (d₁ : ModDualityDatum A N₁ N₁')
    (d₂ : ModDualityDatum A N₂ N₂') :
    μ[A] ≫ tensorCopair A d₁ d₂ =
      (A ◁ tensorCopair A d₁ d₂) ≫
        modTensorAct A (modTensorMod A N₁ N₂)
          (modTensorMod A N₁' N₂') := by
  rw [tensorCopair, ← Category.assoc, regPairUnfold_act,
    Category.assoc,
    reassoc_of% (modTensorAct_map A d₁.copairMod d₂.copairMod),
    interchangeDesc_act,
    ← MonoidalCategory.whiskerLeft_comp_assoc,
    ← MonoidalCategory.whiskerLeft_comp_assoc,
    Category.assoc]

/-- **The tensor product of duality data** (Deligne 1.15, tensor
part): dual pairs tensor, with the crossed coordinatewise pairing
and copairing. -/
noncomputable def tensorDatum (d₁ : ModDualityDatum A N₁ N₁')
    (d₂ : ModDualityDatum A N₂ N₂') :
    ModDualityDatum A (modTensorMod A N₁ N₂)
      (modTensorMod A N₁' N₂') where
  pair := tensorPair A d₁ d₂
  copair := tensorCopair A d₁ d₂
  pair_linear := tensorPair_linear A d₁ d₂
  copair_linear := tensorCopair_linear A d₁ d₂

end Datum

end RS
