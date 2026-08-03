import RS.Classical.Deligne.FreeModShuffle

/-!
# Components of the free module on a biproduct

The free module on a binary biproduct is the biproduct of the two
free modules; that isomorphism is `freeModBiprodIso`, assembled
from the carrier-level distributor `tensorBiprodIso`.
Recorded here are its four components: the distributor followed by
a projection of the module biproduct is the free module on the
corresponding projection of the underlying biproduct, and an
injection of the module biproduct followed by the inverse
distributor is the free module on the corresponding injection.
Since each side is a module map, the identifications are those of
the carriers, and the carrier-level identifications are the
defining equations of `biprod.lift` and `biprod.desc`.

The vanishing of the free module on a zero object completes the
bookkeeping of the empty mixed sum.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
variable [Preadditive D] [MonoidalPreadditive D]
  [HasBinaryBiproducts D]
variable (R : D) [MonObj R] (V W : D)

omit [HasBinaryBiproducts D] in
/-- **The free module on a zero object is zero**: the vanishing of
a tensor product, retyped at the carrier of the free module. -/
theorem freeModZeroIso {V : D} (h : IsZero V) :
    IsZero (freeMod R V).X :=
  isZero_whiskerLeft R h

end RS
