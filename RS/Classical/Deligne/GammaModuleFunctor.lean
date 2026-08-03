import RS.Classical.Deligne.SuperModHom

/-!
# Realization as a functor on module objects

Taking the morphisms out of the two generators is functorial on
module objects over a fixed commutative monoid object: the
realization of a module map is postcomposition.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits

universe v u

variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  [SymmetricCategory D] [Preadditive D] [MonoidalPreadditive D]
  [CategoryTheory.Linear ℂ D] [MonoidalLinear ℂ D]

/-- **Realization, as a functor on module objects.** -/
noncomputable def gammaModuleFunctor (L : OddLine D) (R : D)
    [MonObj R] [IsCommMonObj R] :
    Mod D R ⥤ (gammaAlgebra D L R).Mod where
  obj M := gammaModule D L R M.X
  map {_ _} f :=
    letI : IsModHom R f.hom := f.isModHom
    gammaModuleMap L R f.hom
  map_id M := by
    refine SuperCommAlgebra.Mod.Hom.ext ?_ ?_ <;>
      refine LinearMap.ext fun m => ?_ <;>
      · show m ≫ Mod.Hom.hom (𝟙 M) = m
        rw [Mod.id_hom', Category.comp_id]
  map_comp {M N P} f g := by
    refine SuperCommAlgebra.Mod.Hom.ext ?_ ?_ <;>
      refine LinearMap.ext fun m => ?_ <;>
      · show m ≫ Mod.Hom.hom (f ≫ g) = (m ≫ f.hom) ≫ g.hom
        rw [Mod.comp_hom', Category.assoc]

end RS
