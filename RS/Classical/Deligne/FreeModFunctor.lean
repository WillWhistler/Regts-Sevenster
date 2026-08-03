import RS.Classical.Deligne.FibreFunctor
import RS.Classical.Deligne.GammaModuleFunctor

/-!
# The free-module functor, and the factorisation of `ω`

Base change to an algebra is a functor to the module objects over
that algebra, and Deligne's `ω` of 2.11 is that functor followed by
realization.  Recording the factorisation lets the two halves be
treated separately: the free-module functor carries the monoidal
comparison of the ambient category, and realization carries the
comparison of (2.11.1).
-/

namespace RS

open CategoryTheory MonoidalCategory Limits

universe v u

section Free

variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
variable (A : D) [MonObj A]

/-- Base change of a morphism is the identity on the identity. -/
theorem freeModMap_id (V : D) :
    freeModMap A (𝟙 V) = 𝟙 (freeMod A V) := by
  apply Mod.Hom.ext
  exact MonoidalCategory.whiskerLeft_id A V

/-- Base change of a morphism respects composition. -/
theorem freeModMap_comp {V W X : D} (f : V ⟶ W) (g : W ⟶ X) :
    freeModMap A (f ≫ g) = freeModMap A f ≫ freeModMap A g := by
  apply Mod.Hom.ext
  exact MonoidalCategory.whiskerLeft_comp A f g

/-- **Base change to an algebra, as a functor.** -/
noncomputable def freeModFunctor : D ⥤ Mod D A where
  obj V := freeMod A V
  map f := freeModMap A f
  map_id := freeModMap_id A
  map_comp := freeModMap_comp A

@[simp] theorem freeModFunctor_obj (V : D) :
    (freeModFunctor A).obj V = freeMod A V := rfl

@[simp] theorem freeModFunctor_map {V W : D} (f : V ⟶ W) :
    (freeModFunctor A).map f = freeModMap A f := rfl

end Free

end RS
