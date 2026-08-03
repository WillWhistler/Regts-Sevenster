import RS.Classical.Deligne.SandwichZig
import RS.Classical.Deligne.ModPowDescentClose
import RS.Classical.Deligne.TrichotomyClose

/-!
# The power descent, unconditionally

Over a zigzag datum the sandwich retract exists, so vanishing of
a relative tensor power descends to the module itself.
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
variable (A : D) [MonObj A] [IsCommMonObj A]

/-- **Power vanishing descends to the module** (Deligne 2.9,
case (c), object half): over a duality datum with the zigzag
laws, a module whose `(k + 2)`-nd relative power vanishes is
zero. -/
theorem isZero_of_isZero_modPow {M M' : Mod D A}
    (d : ModDualityDatum A M M') (hz : ModZigzagDatum A d)
    (k : ℕ) (h : IsZero (modPow A M.X (k + 2))) :
    IsZero M.X :=
  isZero_of_sandwich_of_isZero_modPow A M M'
    (sandwichIns A d) (sandwichCon A d)
    (sandwichIns_sandwichCon A d hz) h

section Trichotomy

variable [Linear ℂ D] [MonoidalLinear ℂ D]

/-- **The dévissage trichotomy** (Deligne 2.9, the case
analysis): over any state, either every symmetric power of the
remainder survives, or every alternating power survives, or the
remainder is zero. -/
theorem devissageTrichotomy (P : SchurPackage.{v})
    (L : OddLine D) (X : D) :
    DevissageTrichotomy D L X :=
  devissageTrichotomy_of_descent P L X
    (fun B _ _ _ _ d hz k h =>
      isZero_of_isZero_modPow B d hz k h)

end Trichotomy

end RS
