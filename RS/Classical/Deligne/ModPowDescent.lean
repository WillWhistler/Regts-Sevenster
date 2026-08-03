import RS.Classical.Deligne.PowCopairing
import RS.Classical.Deligne.ModZero

/-!
# The retract tower of a dualizable module

Iterating the zig retract: a module that is a retract of its
double-dual sandwich is a retract of every stage of the sandwich
tower.  Together with the merge isomorphisms this descends the
vanishing of a relative power to the module itself.
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
variable (M M' : Mod D A)

/-- **The sandwich tower**: iterate tensoring with the pair
`M ⊗ M'` on the left. -/
noncomputable def sandwichTower : ℕ → Mod D A
  | 0 => M
  | (k + 1) => modTensorMod A (modTensorMod A M M')
      (sandwichTower k)

omit [Preadditive D] [MonoidalPreadditive D]
  [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair
    (tensorRight Z)] in
@[simp] lemma sandwichTower_zero :
    sandwichTower A M M' 0 = M := rfl

omit [Preadditive D] [MonoidalPreadditive D]
  [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair
    (tensorRight Z)] in
@[simp] lemma sandwichTower_succ (k : ℕ) :
    sandwichTower A M M' (k + 1) =
      modTensorMod A (modTensorMod A M M')
        (sandwichTower A M M' k) := rfl

omit [Preadditive D] [MonoidalPreadditive D]
  [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair
    (tensorRight Z)] in
/-- **The retract iterates up the tower**: a module that is a
retract of its sandwich is a retract of every tower stage. -/
theorem sandwichTower_retract
    (i₀ : M ⟶ modTensorMod A (modTensorMod A M M') M)
    (r₀ : modTensorMod A (modTensorMod A M M') M ⟶ M)
    (h₀ : i₀ ≫ r₀ = 𝟙 M) :
    ∀ k : ℕ, ∃ (i : M ⟶ sandwichTower A M M' k)
      (r : sandwichTower A M M' k ⟶ M), i ≫ r = 𝟙 M
  | 0 => ⟨𝟙 M, 𝟙 M, Category.id_comp _⟩
  | (k + 1) => by
    obtain ⟨ik, rk, hk⟩ :=
      sandwichTower_retract i₀ r₀ h₀ k
    refine ⟨i₀ ≫ modTensorMapMod A (𝟙 _) ik,
      modTensorMapMod A (𝟙 _) rk ≫ r₀, ?_⟩
    have hmid : modTensorMapMod A
        (𝟙 (modTensorMod A M M')) ik ≫
        modTensorMapMod A (𝟙 (modTensorMod A M M')) rk =
        𝟙 (modTensorMod A (modTensorMod A M M') M) := by
      apply Mod.Hom.ext
      show modTensorMap A (𝟙 (modTensorMod A M M')) ik ≫
        modTensorMap A (𝟙 (modTensorMod A M M')) rk =
        𝟙 (modTensor A (modTensorMod A M M') M)
      rw [← modTensorMap_comp, Category.comp_id]
      have hcarrier : ik ≫ rk = 𝟙 M := hk
      rw [hcarrier, modTensorMap_id]
    rw [Category.assoc]
    refine Eq.trans (whisker_eq _
      (Category.assoc _ _ _).symm) ?_
    refine Eq.trans (whisker_eq _ (eq_whisker hmid _)) ?_
    refine Eq.trans (whisker_eq _ (Category.id_comp _)) ?_
    exact h₀

end RS
