import RS.StatementForward
import RS.StatementQuant
import RS.StatementConverse
import RS.Classical.Interfaces.DeligneTheorem

/-!
# The certification challenge

The six theorems of record, stated with `sorry`, for verification
by [comparator](https://github.com/leanprover/comparator): the
checker builds this module and `Solution.lean` separately, confirms
at the kernel-export level that each theorem below is proved in
`Solution` with an identical statement, checks the proofs against
the axiom whitelist `[propext, Classical.choice, Quot.sound]`
(`comparator-config.json`), and replays the result through the
kernel.  The statements are phrased in the same vocabulary the
statement surface pins (`RS/Assembly/BlueprintStatement.lean`);
this module imports the statement modules only, none of the proofs.

This module deliberately contains `sorry` — that is the challenge
format — so it is not part of the default build target.
-/

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
