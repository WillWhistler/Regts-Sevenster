import RS.Novel.Skein.PathCanon
import RS.Novel.Skein.GlueSplitProof

/-!
# The between-legs parity identity

The abstract heart of the canonical splitting's cut sign: for any
family of chords, the number of chord ends strictly between the
cut labels has the parity of the number of chords crossing the
cut — a nested chord contributes both ends, a crossing chord
exactly one.
-/

namespace RS

open scoped Classical

variable {α : Type} [LinearOrder α]

/-- A chord crosses the cut when exactly one endpoint lies
between the cut labels. -/
def CrossesCut (i j : α) (p : α × α) : Prop :=
  Xor (i < p.1 ∧ p.1 < j) (i < p.2 ∧ p.2 < j)

end RS
