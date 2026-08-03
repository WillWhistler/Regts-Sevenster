import RS.Classical.Deligne.ModMultiTriple
import RS.Classical.Deligne.ZigzagSandwich

/-!
# The sandwich retract of the zig triangle

Over a zigzag datum the sandwich insertion is a section of the
sandwich contraction: the module is a retract of its double-dual
sandwich.  The two legs are read on the carrier, where the zig
triangle already lives; `RS.Classical.Deligne.ZigzagSandwich`
supplies those two readings, `RS.sandwichIns_hom` and
`RS.modTensorπ_sandwichCon`.
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
variable {M M' : Mod D A}

/-- **The sandwich retract**: over a zigzag datum the sandwich
insertion is a section of the sandwich contraction. -/
theorem sandwichIns_sandwichCon (d : ModDualityDatum A M M')
    (hz : ModZigzagDatum A d) :
    sandwichIns A d ≫ sandwichCon A d = 𝟙 M := by
  apply Mod.hom_ext
  have hcar := zig_carrier_of_multi A d.copair d.pair
    d.pair_linear hz.zig
  refine Eq.trans ?_ hcar
  show (sandwichIns A d).hom ≫ (sandwichCon A d).hom = _
  refine Eq.trans (eq_whisker (sandwichIns_hom A d) _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine whisker_eq _ ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  exact whisker_eq _ (modTensorπ_sandwichCon A d)

end RS
