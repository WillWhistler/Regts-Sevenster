import RS.Classical.Deligne.BaseChangeLinear
import RS.Classical.Deligne.FreeModShuffle

/-!
# The base change of a duality datum

The pairing and copairing of a duality datum base-change to a
duality datum over the new base: the projection formula, the
functorial maps and the unit collapses are all linear, so the
composites defining the base-changed pairing and copairing are
linear too.
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
variable (B : D) [MonObj B] [IsCommMonObj B]
variable (φ : A ⟶ B) [IsMonHom φ]
variable {M M' : Mod D A}

/-- **The base-changed pairing is linear.** -/
theorem baseChangePair_linear (d : ModDualityDatum A M M') :
    modTensorAct B (baseChangeMod φ M')
        (baseChangeMod φ M) ≫ baseChangePair A B φ d =
      (B ◁ baseChangePair A B φ d) ≫ μ[B] := by
  show modTensorAct B (baseChangeMod φ M')
      (baseChangeMod φ M) ≫
      ((projFormula A B φ M' M).hom ≫
        modTensorMap A (𝟙 (restrictRegular φ)) (d.pairMod) ≫
        (modTensorUnitRight A (restrictRegular φ)).hom) =
    (B ◁ ((projFormula A B φ M' M).hom ≫
      modTensorMap A (𝟙 (restrictRegular φ)) (d.pairMod) ≫
      (modTensorUnitRight A (restrictRegular φ)).hom)) ≫ μ[B]
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker
    (projFormula_linear A B φ M' M) _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (whisker_eq _
    (Category.assoc _ _ _).symm) ?_
  refine Eq.trans (whisker_eq _ (eq_whisker
    (baseChangeAct_modTensorMap A B φ (d.pairMod)) _)) ?_
  refine Eq.trans (whisker_eq _ (Category.assoc _ _ _)) ?_
  refine Eq.trans (whisker_eq _ (whisker_eq _
    (baseChangeAct_unitRight A B φ))) ?_
  refine Eq.symm ?_
  refine Eq.trans (eq_whisker
    (MonoidalCategory.whiskerLeft_comp B _ _) _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine whisker_eq _ ?_
  refine Eq.trans (eq_whisker
    (MonoidalCategory.whiskerLeft_comp B _ _) _) ?_
  exact Category.assoc _ _ _

/-- **The base-changed copairing is linear.** -/
theorem baseChangeCopair_linear (d : ModDualityDatum A M M') :
    μ[B] ≫ baseChangeCopair A B φ d =
      (B ◁ baseChangeCopair A B φ d) ≫
        modTensorAct B (baseChangeMod φ M)
          (baseChangeMod φ M') := by
  have hu : μ[B] ≫
      (modTensorUnitRight A (restrictRegular φ)).inv =
      (B ◁ (modTensorUnitRight A (restrictRegular φ)).inv) ≫
        baseChangeAct φ (regularMod A) := by
    refine act_inv_of_act_hom B
      (modTensorUnitRight A (restrictRegular φ)) ?_
    exact baseChangeAct_unitRight A B φ
  have hp : baseChangeAct φ (modTensorMod A M M') ≫
      (projFormula A B φ M M').inv =
      (B ◁ (projFormula A B φ M M').inv) ≫
        modTensorAct B (baseChangeMod φ M)
          (baseChangeMod φ M') := by
    refine act_inv_of_act_hom B (projFormula A B φ M M') ?_
    exact projFormula_linear A B φ M M'
  show μ[B] ≫
      ((modTensorUnitRight A (restrictRegular φ)).inv ≫
        modTensorMap A (𝟙 (restrictRegular φ))
          (d.copairMod) ≫
        (projFormula A B φ M M').inv) =
    (B ◁ ((modTensorUnitRight A (restrictRegular φ)).inv ≫
      modTensorMap A (𝟙 (restrictRegular φ))
        (d.copairMod) ≫
      (projFormula A B φ M M').inv)) ≫
      modTensorAct B (baseChangeMod φ M) (baseChangeMod φ M')
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker hu _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (whisker_eq _
    (Category.assoc _ _ _).symm) ?_
  refine Eq.trans (whisker_eq _ (eq_whisker
    (baseChangeAct_modTensorMap A B φ (d.copairMod)) _)) ?_
  refine Eq.trans (whisker_eq _ (Category.assoc _ _ _)) ?_
  refine Eq.trans (whisker_eq _ (whisker_eq _ hp)) ?_
  refine Eq.symm ?_
  refine Eq.trans (eq_whisker
    (MonoidalCategory.whiskerLeft_comp B _ _) _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine whisker_eq _ ?_
  refine Eq.trans (eq_whisker
    (MonoidalCategory.whiskerLeft_comp B _ _) _) ?_
  exact Category.assoc _ _ _

/-- **The base change of a duality datum.** -/
noncomputable def baseChangeDatum (d : ModDualityDatum A M M') :
    ModDualityDatum B (baseChangeMod φ M)
      (baseChangeMod φ M') where
  pair := baseChangePair A B φ d
  copair := baseChangeCopair A B φ d
  pair_linear := baseChangePair_linear A B φ d
  copair_linear := baseChangeCopair_linear A B φ d

section Unit

/-- **The unit of the base-change structure**: the base change of
the regular module is the regular module over the new base. -/
noncomputable def baseChangeUnitIso :
    baseChangeMod φ (regularMod A) ≅ regularMod B where
  hom := Mod.Hom.mk'
    (modTensorUnitRight A (restrictRegular φ)).hom (by
      exact baseChangeAct_unitRight A B φ)
  inv := Mod.Hom.mk'
    (modTensorUnitRight A (restrictRegular φ)).inv (by
      exact act_inv_of_act_hom B
        (modTensorUnitRight A (restrictRegular φ))
        (baseChangeAct_unitRight A B φ))
  hom_inv_id := by
    apply Mod.Hom.ext
    exact (modTensorUnitRight A (restrictRegular φ)).hom_inv_id
  inv_hom_id := by
    apply Mod.Hom.ext
    exact (modTensorUnitRight A (restrictRegular φ)).inv_hom_id

end Unit

end RS
