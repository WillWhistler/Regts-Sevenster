import RS.StatementForward

/-!
# The quantitative Regts–Sevenster statement surface

The main statement with the paper's displayed dimension bound: the
mixed functional can be chosen with even dimension `k` and odd
dimension `2ℓ` both at most `⌊2eR⌋` (Corollary 4.10 of the
accompanying paper).  The unbounded statement follows by forgetting
the bounds.
-/

namespace RS

/-- A mixed partition function with explicit dimension bounds: the
functional's even dimension `k` and odd dimension `2ℓ` are both at
most `B`. -/
def IsMixedPartitionFunctionBounded (f : ClosedFragment → ℂ)
    (B : ℕ) : Prop :=
  ∃ (k ℓ : ℕ) (h : MixedFunctional k ℓ),
    k ≤ B ∧ 2 * ℓ ≤ B ∧
      ∀ W : ClosedFragment, f W = mixedPartition h W

/-- **THE QUANTITATIVE REGTS–SEVENSTER STATEMENT**: every graph
parameter with edge-connection rank at most `R ^ t` is a mixed
partition function of a `(k, 2ℓ)`-functional with
`k, 2ℓ ≤ ⌊2eR⌋`. -/
def RegtsSevensterStatementQuant : Prop :=
  ∀ (R : ℕ) (f : EdgeRankParameter R),
    IsMixedPartitionFunctionBounded f.val
      ⌊2 * Real.exp 1 * (R : ℝ)⌋₊

end RS
