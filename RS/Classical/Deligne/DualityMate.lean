import RS.Common.MathlibDeps

/-!
# Duality-intertwining morphisms are invertible

The per-object kernel of Deligne 3.2: a morphism compatible with
exact pairings on both sides is an isomorphism, with inverse the
mate of its partner.  A monoidal natural transformation between
fibre functors supplies exactly this data at every object.
-/

namespace RS

open CategoryTheory MonoidalCategory

universe v u

variable {D : Type u} [Category.{v} D] [MonoidalCategory D]

/-- The mate of the partner: the candidate inverse. -/
noncomputable def dualityMate {X X' Y Y' : D}
    [ExactPairing X X'] [ExactPairing Y Y'] (f' : X' ⟶ Y') :
    Y ⟶ X :=
  (λ_ Y).inv ≫ (η_ X X' ▷ Y) ≫ (α_ X X' Y).hom ≫
    (X ◁ (f' ▷ Y)) ≫ (X ◁ ε_ Y Y') ≫ (ρ_ X).hom

end RS
