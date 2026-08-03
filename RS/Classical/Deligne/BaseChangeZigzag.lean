import RS.Classical.Deligne.BaseChangeDatum

/-!
# The zigzag laws of a base-changed duality datum

The statement that base change preserves the zigzag laws, named
so that the dévissage steps can refer to it directly.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  [SymmetricCategory D]
variable [Preadditive D] [MonoidalPreadditive D]
  [HasFiniteBiproducts D] [HasCoequalizers D]
variable [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair
  (tensorLeft Z)]
variable [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair
  (tensorRight Z)]

/-- **Base change preserves the zigzag laws**: the statement of
record for the dévissage steps. -/
def BaseChangeZigzagStatement : Prop :=
  ∀ (A : D) (_ : MonObj A) (_ : IsCommMonObj A)
    (M M' : Mod D A) (d : ModDualityDatum A M M')
    (_ : ModZigzagDatum A d)
    (B : D) (_ : MonObj B) (_ : IsCommMonObj B)
    (φ : A ⟶ B) (_ : IsMonHom φ),
    ModZigzagDatum B (baseChangeDatum A B φ d)

end RS
