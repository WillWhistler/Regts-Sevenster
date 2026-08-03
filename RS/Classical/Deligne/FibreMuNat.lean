import RS.Classical.Deligne.FibreMu

/-!
# Naturality of the monoidal comparison of the fibre functor

The free-module shuffle is natural in its two variables, and the
monoidal comparison of the fibre functor inherits that naturality
directly on the generators of the tensor product of super modules.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

section Shuffle

variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
variable [BraidedCategory D] (R : D) [MonObj R]

/-- **The free-module shuffle is natural.** -/
theorem freeModShuffle_naturality {V V' W W' : D} (f : V ⟶ V')
    (g : W ⟶ W') :
    ((R ◁ f) ⊗ₘ (R ◁ g)) ≫ freeModShuffle R V' W' =
      freeModShuffle R V W ≫ (R ◁ (f ⊗ₘ g)) := by
  have h := tensorμ_natural (C := D) (𝟙 R) f (𝟙 R) g
  simp only [id_tensorHom, MonoidalCategory.whiskerLeft_id] at h
  show ((R ◁ f) ⊗ₘ (R ◁ g)) ≫
      tensorμ R V' R W' ≫ μ[R] ▷ (V' ⊗ W') =
    (tensorμ R V R W ≫ μ[R] ▷ (V ⊗ W)) ≫ (R ◁ (f ⊗ₘ g))
  rw [← Category.assoc, h, Category.assoc, Category.assoc]
  exact whisker_eq _ (whisker_exchange μ[R] (f ⊗ₘ g))

end Shuffle

section Fibre

variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
variable [SymmetricCategory D] [Preadditive D] [MonoidalPreadditive D]
variable [Linear ℂ D] [MonoidalLinear ℂ D] [HasCoequalizers D]
variable [∀ Z : D,
  PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
variable (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R]

open SuperCommAlgebra.Mod

/-- **The monoidal comparison of the fibre functor is natural.** -/
theorem fibreMu_naturality {V V' W W' : D} (f : V ⟶ V')
    (g : W ⟶ W') :
    SuperCommAlgebra.Mod.tensorHom
        (gammaFunMap L R (freeModMap R f))
        (gammaFunMap L R (freeModMap R g)) ≫
        fibreMu L R V' W' =
      fibreMu L R V W ≫
        gammaFunMap L R (freeModMap R (f ⊗ₘ g)) := by
  have hint : ∀ {X Y : D} (m : X ⟶ R ⊗ V) (n : Y ⟶ R ⊗ W),
      ((m ≫ R ◁ f) ⊗ₘ (n ≫ R ◁ g)) ≫ freeModShuffle R V' W' =
        ((m ⊗ₘ n) ≫ freeModShuffle R V W) ≫
          R ◁ (f ⊗ₘ g) := by
    intro X Y m n
    rw [Category.assoc, ← freeModShuffle_naturality R f g,
      ← Category.assoc, tensorHom_comp_tensorHom]
  refine hom_ext (fun m n => ?_) (fun m n => ?_) (fun m n => ?_)
    (fun m n => ?_)
  · have hl : (SuperCommAlgebra.Mod.tensorHom
        (gammaFunMap L R (freeModMap R f))
        (gammaFunMap L R (freeModMap R g)) ≫
        fibreMu L R V' W').evenMap (tmulEE _ _ m n) =
      (fibreMu L R V' W').evenMap
        (tmulEE _ _ (m ≫ R ◁ f) (n ≫ R ◁ g)) := by
      rw [comp_evenMap_apply, tensorHom_evenMap_tmulEE]
      rfl
    rw [hl, fibreMu_evenMap_tmulEE, comp_evenMap_apply,
      fibreMu_evenMap_tmulEE]
    exact Eq.trans (whisker_eq _ (hint m n))
      (Category.assoc _ _ _).symm
  · have hl : (SuperCommAlgebra.Mod.tensorHom
        (gammaFunMap L R (freeModMap R f))
        (gammaFunMap L R (freeModMap R g)) ≫
        fibreMu L R V' W').evenMap (tmulOO _ _ m n) =
      (fibreMu L R V' W').evenMap
        (tmulOO _ _ (m ≫ R ◁ f) (n ≫ R ◁ g)) := by
      rw [comp_evenMap_apply, tensorHom_evenMap_tmulOO]
      rfl
    rw [hl, fibreMu_evenMap_tmulOO, comp_evenMap_apply,
      fibreMu_evenMap_tmulOO]
    exact Eq.trans (whisker_eq _ (hint m n))
      (Category.assoc _ _ _).symm
  · have hl : (SuperCommAlgebra.Mod.tensorHom
        (gammaFunMap L R (freeModMap R f))
        (gammaFunMap L R (freeModMap R g)) ≫
        fibreMu L R V' W').oddMap (tmulEO _ _ m n) =
      (fibreMu L R V' W').oddMap
        (tmulEO _ _ (m ≫ R ◁ f) (n ≫ R ◁ g)) := by
      rw [comp_oddMap_apply, tensorHom_oddMap_tmulEO]
      rfl
    rw [hl, fibreMu_oddMap_tmulEO, comp_oddMap_apply,
      fibreMu_oddMap_tmulEO]
    exact Eq.trans (whisker_eq _ (hint m n))
      (Category.assoc _ _ _).symm
  · have hl : (SuperCommAlgebra.Mod.tensorHom
        (gammaFunMap L R (freeModMap R f))
        (gammaFunMap L R (freeModMap R g)) ≫
        fibreMu L R V' W').oddMap (tmulOE _ _ m n) =
      (fibreMu L R V' W').oddMap
        (tmulOE _ _ (m ≫ R ◁ f) (n ≫ R ◁ g)) := by
      rw [comp_oddMap_apply, tensorHom_oddMap_tmulOE]
      rfl
    rw [hl, fibreMu_oddMap_tmulOE, comp_oddMap_apply,
      fibreMu_oddMap_tmulOE]
    exact Eq.trans (whisker_eq _ (hint m n))
      (Category.assoc _ _ _).symm

end Fibre

end RS
