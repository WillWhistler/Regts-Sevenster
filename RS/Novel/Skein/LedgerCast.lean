import RS.Novel.Skein.LedgerStage

/-!
# Transporting a subset's data along an equality

The interface recursion glues with `Fragment.gluePair`, which
dispatches on whether the two glued flags already bound a common
edge.  Each branch identifies the glued fragment with the one the
per-glue lemmas are stated for, and the subset, the transition system
and the ledger's two counts have to be carried across that
identification.

Nothing here is more than `subst`: the transports exist so the
recursion can name them rather than unfold them.
-/

namespace RS

namespace EdgeSubset

open Fragment Equiv Classical

section SubsetEq

variable {β : Type} [LinearOrder β] {V : Fragment β}
  {F F' : EdgeSubset V} (hF : F = F')

/-- Transport a transition system along an equality of subsets. -/
def relOfEq (κ : F.RelTransitionSystem) : F'.RelTransitionSystem := by
  subst hF; exact κ

/-- Transport an orientation along an equality of subsets. -/
def orientOfEq {κ : F.RelTransitionSystem} (o : κ.Orientation) :
    (relOfEq hF κ).Orientation := by
  subst hF; exact o

omit [LinearOrder β] in
/-- Transporting a system along an equality of subsets does not
change its circuit count. -/
theorem openCircuitCount_relOfEq [Fintype β]
    (κ : F.RelTransitionSystem) :
    (relOfEq hF κ).openCircuitCount = κ.openCircuitCount := by
  subst hF; rfl

omit [LinearOrder β] in
/-- Nor its boundary pairing. -/
theorem chordInv_relOfEq (κ : F.RelTransitionSystem) (a : β) :
    chordInv F' (relOfEq hF κ) a = chordInv F κ a := by
  subst hF; rfl

omit [LinearOrder β] in
include hF in
/-- Nor whether the subset uses interface pairs together. -/
theorem swapPaired_of_eq (ι : β → β) (h : SwapPaired F ι) :
    SwapPaired F' ι := by
  subst hF; exact h

end SubsetEq

end EdgeSubset

end RS
