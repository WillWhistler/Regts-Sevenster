import RS.Classical.Deligne.SignConj
import RS.Classical.Deligne.TrichotomyClose

/-!
# Symmetric powers of an odd twist

Twisting a module by the odd line exchanges the two halves of
the trichotomy: the symmetric powers of the twist survive
exactly when the alternating powers of the module do.  In arity
zero both are the tensor unit, so the exchange holds there
too.
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
variable [CategoryTheory.Linear ℂ D] [MonoidalLinear ℂ D]
variable (A : D) [MonObj A] [IsCommMonObj A]

/-- **Surviving alternating powers become surviving symmetric
powers after the odd twist.** -/
theorem not_isZero_symPow_twist (L : OddLine D) (R : Mod D A)
    (hA : ∀ n : ℕ, ¬ IsZero (altPow A R.X n)) (n : ℕ) :
    ¬ IsZero (symPow A ((tensorLeftMod A L.obj R).X) n) := by
  cases n with
  | zero =>
    intro h
    exact hA 0 (isZero_of_isZero_unit _
      (h.of_iso
        (symPowZero A ((tensorLeftMod A L.obj R).X)).symm))
  | succ k =>
    intro h
    exact hA (k + 1) ((symPowOddTwist_isZero_iff A L R k).mp h)

end RS
