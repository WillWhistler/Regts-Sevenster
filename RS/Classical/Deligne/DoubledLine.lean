import RS.Classical.Deligne.Doubling
import RS.Classical.Deligne.Prop29

/-!
# The odd line of the doubling

The ℤ/2-graded doubling of a tensor category always contains an
odd line: the monoidal unit placed in odd degree squares to the
unit and self-braids by `−1`.  This is Deligne's device for the
general case of 2.11, where the category itself need not contain
such an object.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits

universe v u

variable {A : Type u} [Category.{v} A] [MonoidalCategory A]
  [SymmetricCategory A] [Preadditive A] [MonoidalPreadditive A]
  [HasBinaryBiproducts A] [HasZeroObject A]

/-- **The odd line of the doubling**: the unit in odd degree. -/
noncomputable def doubledOddLine : OddLine (Doubled A) where
  obj := Doubled.oddUnit
  sq := Doubled.oddUnitSq
  braid_neg := Doubled.braiding_oddUnit

end RS
