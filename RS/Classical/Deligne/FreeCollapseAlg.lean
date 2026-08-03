import RS.Classical.Deligne.FreePow

/-!
# The collapse against the group-algebra action

Permutation equivariance of the free collapse extends linearly to
the whole symmetric-group algebra: the action on a word of free
letters becomes, after collapsing the heads, the action on the
ambient word under the head.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  [SymmetricCategory D] [Preadditive D] [MonoidalPreadditive D]
  [Linear ℂ D] [MonoidalLinear ℂ D]
variable (A : D) [MonObj A] [IsCommMonObj A] (V : D)

omit [SymmetricCategory D] [Linear ℂ D] [MonoidalLinear ℂ D]
  [IsCommMonObj A] in
/-- Passing a sum across a collapse-type intertwiner. -/
private theorem add_pass_free {P W Y : D} {T : P ⟶ W ⊗ Y}
    {u v : P ⟶ P} {u' v' : Y ⟶ Y}
    (hu : u ≫ T = T ≫ (W ◁ u'))
    (hv : v ≫ T = T ≫ (W ◁ v')) :
    (u + v) ≫ T = T ≫ (W ◁ (u' + v')) := by
  rw [Preadditive.add_comp, hu, hv,
    MonoidalPreadditive.whiskerLeft_add, Preadditive.comp_add]

omit [SymmetricCategory D] [IsCommMonObj A] in
/-- Passing a scalar across a collapse-type intertwiner. -/
private theorem smul_pass_free {P W Y : D} {T : P ⟶ W ⊗ Y}
    {u : P ⟶ P} {u' : Y ⟶ Y} (r : ℂ)
    (h : u ≫ T = T ≫ (W ◁ u')) :
    (r • u) ≫ T = T ≫ (W ◁ (r • u')) := by
  rw [Linear.smul_comp, h, MonoidalLinear.whiskerLeft_smul,
    Linear.comp_smul]

/-- **Equivariance of the collapse for the group algebra.** -/
theorem freeCollapse_permAlg (n : ℕ) (z : SymGroupAlgebra n) :
    (permAlg (A ⊗ V) n z : tensorPow D (A ⊗ V) n ⟶
        tensorPow D (A ⊗ V) n) ≫ freeCollapse A V n =
      freeCollapse A V n ≫
        (A ◁ (permAlg V n z : tensorPow D V n ⟶
          tensorPow D V n)) := by
  induction z using MonoidAlgebra.induction_on with
  | hM σ =>
    rw [show (MonoidAlgebra.of ℂ (Equiv.Perm (Fin n))) σ =
        MonoidAlgebra.single σ (1 : ℂ) from rfl, permAlg_single,
      permAlg_single]
    exact freeCollapse_permMor A V n σ
  | hadd z₁ z₂ h₁ h₂ =>
    rw [map_add, map_add]
    exact add_pass_free h₁ h₂
  | hsmul r z h =>
    rw [map_smul, map_smul]
    exact smul_pass_free r h

end RS
