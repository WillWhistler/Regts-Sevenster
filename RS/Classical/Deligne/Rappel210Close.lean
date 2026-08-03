import RS.Classical.Deligne.Rappel210Bridge
import RS.Classical.Deligne.Rappel210Reduce

/-!
# The local splitting statement, up to unit nonvanishing

The assembly of the local splitting statement: the splitting
algebra of the dualised unit-form point, with its class and the
restriction identity, feeds the reduction.  What remains at each
consumer is the nonvanishing of the algebra's unit, which over an
ind-category follows from the stage units through the filtered
criterion.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  [SymmetricCategory D]
variable [Abelian D] [MonoidalPreadditive D]
variable [HasFiniteBiproducts D] [HasCoequalizers D]
variable [CategoryTheory.Linear ℂ D] [MonoidalLinear ℂ D]
variable [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair
  (tensorLeft Z)]
variable [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair
  (tensorRight Z)]
variable [HasColimitsOfShape SmallNat.{v} D]
variable [∀ Z : D, PreservesColimitsOfShape SmallNat.{v}
  (tensorLeft Z)]
variable [∀ Z : D, PreservesColimitsOfShape SmallNat.{v}
  (tensorRight Z)]
variable (S : ShortComplex D) [HasRightDual (S.X₃ : D)]
variable [HasRightDual (unitFormMid S : D)]

/-- The splitting algebra of a short exact sequence: the local
splitting chain of the dualised unit-form point. -/
noncomputable def rappel210Algebra : D :=
  splitAlgebra ((unitFormMid S)ᘁ) (unitFormPoint S)

omit [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair
    (tensorRight Z)] in
/-- **The local splitting statement holds once the unit of the
splitting algebra survives**: the class of the dual middle object
restricts on the point to the unit, so the reduction applies. -/
theorem rappel210_of_unit_nonzero (hS : S.ShortExact)
    (hnz : splitAlgebraUnit ((unitFormMid S)ᘁ)
      (unitFormPoint S) ≠ 0) :
    Rappel210Statement S hS := by
  letI : MonObj (rappel210Algebra S) :=
    splitAlgebraMonObj (((unitFormMid S)ᘁ : D))
      (unitFormPoint S)
  haveI : IsCommMonObj (rappel210Algebra S) :=
    splitAlgebra_isCommMonObj (((unitFormMid S)ᘁ : D))
      (unitFormPoint S)
  exact rappel210_of_class S hS (rappel210Algebra S) hnz
    (splitCls (((unitFormMid S)ᘁ : D)) (unitFormPoint S))
    (splitCls_point (((unitFormMid S)ᘁ : D))
      (unitFormPoint S))

end RS
