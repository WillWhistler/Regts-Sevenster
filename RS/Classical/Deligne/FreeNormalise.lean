import RS.Classical.Deligne.FreeNormaliseStep
import RS.Classical.Deligne.FreeNormaliseBase
import RS.Classical.Deligne.ModPowStage
import RS.Classical.Deligne.FreePowDesc
import RS.Classical.Deligne.FreeCollapseAlg

/-!
# The relative power of a free module

Gathering every head of a word of free letters onto the last
letter is invisible in the module power: one letter at a time, it
is a slide, and a slide is a slot relation.  So the descended
collapse is an isomorphism
`modPow A (A ⊗ V) (n + 1) ≅ A ⊗ tensorPow D V (n + 1)`,
and under it the descended group-algebra action becomes the
ambient action under the head.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  [SymmetricCategory D] [Preadditive D] [MonoidalPreadditive D]
  [HasFiniteBiproducts D] [HasCoequalizers D]
  [Linear ℂ D] [MonoidalLinear ℂ D]
variable [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair
  (tensorRight Z)]
variable (A : D) [MonObj A] [IsCommMonObj A] (V : D)

omit [Linear ℂ D] [MonoidalLinear ℂ D] in
/-- **Normalisation**: gathering every head onto the last letter
is invisible in the module power. -/
theorem freeNormalise (n : ℕ) :
    (freeCollapse A V (n + 1) ≫ freeInsert A V n) ≫
        modPowπ A (freeMod A V).X (n + 1) =
      modPowπ A (freeMod A V).X (n + 1) := by
  induction n with
  | zero =>
    rw [freeCollapse_freeInsert_one, Category.id_comp]
  | succ k ih =>
    rw [freeCollapse_freeInsert_succ]
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (whisker_eq _ (freeSlideTop_modPowπ A V k)) ?_
    exact modPow_invisible_succ A (freeMod A V).X (k + 1) ih

/-- **The section of the descended collapse**: insert the head on
the last letter and project. -/
noncomputable def freeCollapseSection (n : ℕ) :
    A ⊗ tensorPow D V (n + 1) ⟶ modPow A (freeMod A V).X (n + 1) :=
  freeInsert A V n ≫ modPowπ A (freeMod A V).X (n + 1)

omit [MonoidalPreadditive D] [Linear ℂ D] [MonoidalLinear ℂ D]
  [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair
    (tensorRight Z)] in
/-- The section retracts the descended collapse. -/
theorem freeCollapseSection_desc (n : ℕ) :
    freeCollapseSection A V n ≫ freeCollapseDesc A V (n + 1) =
      𝟙 (A ⊗ tensorPow D V (n + 1)) := by
  rw [freeCollapseSection]
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans
    (whisker_eq _ (modPowπ_freeCollapseDesc A V (n + 1))) ?_
  exact freeInsert_freeCollapse A V n

omit [Linear ℂ D] [MonoidalLinear ℂ D] in
/-- The descended collapse retracts the section. -/
theorem freeCollapseDesc_section (n : ℕ) :
    freeCollapseDesc A V (n + 1) ≫ freeCollapseSection A V n =
      𝟙 (modPow A (freeMod A V).X (n + 1)) := by
  apply modPow_hom_ext A (freeMod A V).X
  rw [← Category.assoc, modPowπ_freeCollapseDesc,
    freeCollapseSection, ← Category.assoc]
  refine Eq.trans (freeNormalise A V n) ?_
  exact (Category.comp_id _).symm

omit [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair
  (tensorRight Z)] in
/-- **The identification intertwines the two group-algebra
actions.** -/
theorem freeModPow_alg (n : ℕ) (z : SymGroupAlgebra (n + 1)) :
    freeCollapseSection A V n ≫
        (modPowAlg A (freeMod A V).X (n + 1) z :
          modPow A (freeMod A V).X (n + 1) ⟶
            modPow A (freeMod A V).X (n + 1)) ≫
        freeCollapseDesc A V (n + 1) =
      A ◁ (permAlg V (n + 1) z : tensorPow D V (n + 1) ⟶
        tensorPow D V (n + 1)) := by
  have hmid : modPowπ A (freeMod A V).X (n + 1) ≫
      ((modPowAlg A (freeMod A V).X (n + 1) z :
          modPow A (freeMod A V).X (n + 1) ⟶
            modPow A (freeMod A V).X (n + 1)) ≫
        freeCollapseDesc A V (n + 1)) =
      (permAlg (A ⊗ V) (n + 1) z :
          tensorPow D (A ⊗ V) (n + 1) ⟶
            tensorPow D (A ⊗ V) (n + 1)) ≫
        freeCollapse A V (n + 1) := by
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (eq_whisker
      (modPowπ_permAlg A (freeMod A V).X (n + 1) z) _) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    exact whisker_eq _ (modPowπ_freeCollapseDesc A V (n + 1))
  rw [freeCollapseSection]
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (whisker_eq _ hmid) ?_
  refine Eq.trans
    (whisker_eq _ (freeCollapse_permAlg A V (n + 1) z)) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker (freeInsert_freeCollapse A V n) _) ?_
  exact Category.id_comp _

omit [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair
  (tensorRight Z)] in
/-- **Module-level vanishing gives whiskered ambient
vanishing.** -/
theorem whisker_permAlg_eq_zero (n : ℕ) (hn : n ≠ 0)
    (z : SymGroupAlgebra n)
    (h : (modPowAlg A (freeMod A V).X n z :
      modPow A (freeMod A V).X n ⟶
        modPow A (freeMod A V).X n) = 0) :
    (A ◁ (permAlg V n z : tensorPow D V n ⟶
      tensorPow D V n)) = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [← freeModPow_alg A V k z, h]
  exact Eq.trans (whisker_eq _ Limits.zero_comp) Limits.comp_zero

/-- **Whiskered ambient vanishing gives module-level
vanishing.** -/
theorem modPowAlg_eq_zero (n : ℕ) (hn : n ≠ 0)
    (z : SymGroupAlgebra n)
    (h : (A ◁ (permAlg V n z : tensorPow D V n ⟶
      tensorPow D V n)) = 0) :
    (modPowAlg A (freeMod A V).X n z :
      modPow A (freeMod A V).X n ⟶
        modPow A (freeMod A V).X n) = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  have hcon := freeModPow_alg A V k z
  rw [h] at hcon
  refine Eq.trans ?_ (Eq.trans (whisker_eq
    (freeCollapseDesc A V (k + 1))
    (Eq.trans (eq_whisker hcon (freeCollapseSection A V k))
      Limits.zero_comp)) Limits.comp_zero)
  simp only [← Category.assoc]
  rw [freeCollapseDesc_section, Category.id_comp]
  simp only [Category.assoc]
  rw [freeCollapseDesc_section, Category.comp_id]

end RS
