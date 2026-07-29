import RS

/-!
# The certification solution

The six theorems of `Challenge.lean`, each proved by the theorem of
record of the same name.  Comparator confirms at the kernel-export
level that the statements match the challenge's, that the proofs
use no axiom outside `[propext, Classical.choice, Quot.sound]`, and
that the kernel accepts them; see `comparator-config.json` and the
CI workflow.
-/

namespace Certified

open RS

/-- **The converse**: every mixed partition function is an
edge-rank-bounded parameter, with base `max 1 (k + 2ℓ)`. -/
theorem regts_sevenster_converse : RegtsSevensterConverseStatement :=
  RS.regts_sevenster_converse

/-- **The forward direction**, conditional on Deligne's theorem
alone. -/
theorem regts_sevenster_deligne_only
    (hDeligne : DeligneTheoremStatement.{1, 1}) :
    RegtsSevensterStatement :=
  RS.regts_sevenster_deligne_only hDeligne

/-- **The quantitative forward direction**, conditional on
Deligne's theorem alone: both dimensions at most `⌊2eR⌋`. -/
theorem regts_sevenster_quant_deligne_only
    (hDeligne : DeligneTheoremStatement.{1, 1}) :
    RegtsSevensterStatementQuant :=
  RS.regts_sevenster_quant_deligne_only hDeligne

/-- **The rank bound from a bounded mixed partition function.** -/
theorem edgeRankBounded_of_mixedBounded
    {f : ClosedFragment → ℂ} {B : ℕ}
    (hf : IsMixedPartitionFunctionBounded f B) :
    EdgeRankBounded f (max 1 (2 * B)) :=
  RS.edgeRankBounded_of_mixedBounded hf

/-- **The characterization**, conditional on Deligne alone: a
fragment parameter has bounded edge rank exactly when it is a mixed
partition function. -/
theorem regts_sevenster_iff
    (hDeligne : DeligneTheoremStatement.{1, 1})
    (f : ClosedFragment → ℂ)
    (hempty : f emptyClosedFragment = 1)
    (hiso : ∀ W₁ W₂ : ClosedFragment, W₁.Equiv W₂ → f W₁ = f W₂) :
    (∃ R : ℕ, EdgeRankBounded f R) ↔ IsMixedPartitionFunction f :=
  RS.regts_sevenster_iff hDeligne f hempty hiso

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
  RS.regts_sevenster_quant_roundtrip hDeligne f hempty hiso

end Certified
