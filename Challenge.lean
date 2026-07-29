import RS.Definitions

/-!
# The certification challenge

The trusted half of an independently checkable certificate for the
six theorems of record, in the format of
[comparator](https://github.com/leanprover/comparator).  This
module imports `RS/Definitions.lean` — the self-contained statement
surface, whose only import is the Mathlib funnel — and states the
six theorems with `sorry`.  `Solution.lean` proves each by the
theorem of record of the same name.

Comparator builds this module and `Solution.lean` separately,
exports both environments at the kernel level, and checks that each
theorem below is proved in the solution with an identical
statement, about identical definitions; that the proofs use no
axiom outside `[propext, Classical.choice, Quot.sound]`
(`comparator-config.json`); and that the kernel replays them.
Reading `RS/Definitions.lean` and this file — against Mathlib
alone — therefore determines exactly what is being certified.

This module deliberately contains `sorry` — that is the challenge
format — so it is not part of the default build target.
-/

/-! ## 12. The six theorems of record

Stated with `sorry`; `Solution.lean` proves each by the theorem of
record of the same name, and comparator certifies the match. -/

namespace Certified

open RS

/-- **The converse**: every mixed partition function is an
edge-rank-bounded parameter, with base `max 1 (k + 2ℓ)`. -/
theorem regts_sevenster_converse : RegtsSevensterConverseStatement :=
  sorry

/-- **The forward direction**, conditional on Deligne's theorem
alone. -/
theorem regts_sevenster_deligne_only
    (hDeligne : DeligneTheoremStatement.{1, 1}) :
    RegtsSevensterStatement :=
  sorry

/-- **The quantitative forward direction**, conditional on
Deligne's theorem alone: both dimensions at most `⌊2eR⌋`. -/
theorem regts_sevenster_quant_deligne_only
    (hDeligne : DeligneTheoremStatement.{1, 1}) :
    RegtsSevensterStatementQuant :=
  sorry

/-- **The rank bound from a bounded mixed partition function.** -/
theorem edgeRankBounded_of_mixedBounded
    {f : ClosedFragment → ℂ} {B : ℕ}
    (hf : IsMixedPartitionFunctionBounded f B) :
    EdgeRankBounded f (max 1 (2 * B)) :=
  sorry

/-- **The characterization**, conditional on Deligne alone: a
fragment parameter has bounded edge rank exactly when it is a mixed
partition function. -/
theorem regts_sevenster_iff
    (hDeligne : DeligneTheoremStatement.{1, 1})
    (f : ClosedFragment → ℂ)
    (hempty : f emptyClosedFragment = 1)
    (hiso : ∀ W₁ W₂ : ClosedFragment, W₁.Equiv W₂ → f W₁ = f W₂) :
    (∃ R : ℕ, EdgeRankBounded f R) ↔ IsMixedPartitionFunction f :=
  sorry

/-- **The quantitative round trip**, conditional on Deligne alone:
edge rank `R` gives dimension `⌊2eR⌋`, and dimension `B` gives edge
rank base `max 1 (2B)`. -/
theorem regts_sevenster_quant_roundtrip
    (hDeligne : DeligneTheoremStatement.{1, 1})
    (f : ClosedFragment → ℂ)
    (hempty : f emptyClosedFragment = 1)
    (hiso : ∀ W₁ W₂ : ClosedFragment, W₁.Equiv W₂ → f W₁ = f W₂) :
    (∀ R, EdgeRankBounded f R →
      IsMixedPartitionFunctionBounded f
        ⌊2 * Real.exp 1 * (R : ℝ)⌋₊) ∧
    (∀ B, IsMixedPartitionFunctionBounded f B →
      EdgeRankBounded f (max 1 (2 * B))) :=
  sorry

end Certified
