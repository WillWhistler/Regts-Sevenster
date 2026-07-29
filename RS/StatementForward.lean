import RS.Novel.Skein.MixedPartition

/-!
# THE REGTS–SEVENSTER CONJECTURE — statement surface

The statement of the main theorem, phrased entirely in the
elementary vocabulary of this development: a graph parameter on
closed fragments (isomorphism-invariant, normalized at the empty
graph) whose connection pairings have rank at most `R ^ t` at every
arity `t` is the mixed partition function of some
`(k, 2ℓ)`-functional in the sense of Regts–Sevenster
(arXiv:1807.04494, Definition 5).

Every notion in the statement is defined in this tree:
`EdgeRankParameter` (`Skein/ConnectionRank.lean`) packages the
hypothesis class, and `IsMixedPartitionFunction`
(`Skein/MixedPartition.lean`) the conclusion.
-/

namespace RS

/-- **THE REGTS–SEVENSTER CONJECTURE.**  Every graph parameter with
exponentially bounded edge-connection rank is a mixed partition
function. -/
def RegtsSevensterStatement : Prop :=
  ∀ (R : ℕ) (f : EdgeRankParameter R), IsMixedPartitionFunction f.val

end RS
