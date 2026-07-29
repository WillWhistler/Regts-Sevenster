import RS.Common.MathlibDeps

/-!
# Conditions on a ℂ-linear category

The three ambient conditions a tensor category is asked to satisfy:
finite-dimensional Hom-spaces, scalar endomorphisms of the tensor
unit, and semisimplicity in the form that every object is a finite
biproduct of simple objects.
-/

namespace RS

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe v u

variable (A : Type u) [Category.{v} A]

/-- Every Hom-space is finite dimensional over ℂ. -/
def HasFinDimHom [Preadditive A] [Linear ℂ A] : Prop :=
  ∀ X Y : A, FiniteDimensional ℂ (X ⟶ Y)

/-- The unit's endomorphisms are the scalars. -/
def HasScalarUnit [Preadditive A] [Linear ℂ A]
    [MonoidalCategory A] : Prop :=
  Function.Bijective
    (fun c : ℂ => (c • 𝟙 (𝟙_ A) : 𝟙_ A ⟶ 𝟙_ A))

/-- Every object is a finite biproduct of simple objects. -/
def IsSemisimple [Preadditive A] [HasFiniteBiproducts A] : Prop :=
  ∀ X : A, ∃ (n : ℕ) (S : Fin n → A),
    (∀ i, Simple (S i)) ∧ Nonempty (X ≅ ⨁ S)

end RS
