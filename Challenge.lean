import RS.Definitions

/-!
# The certification challenge

The trusted half of an independently checkable certificate for the
theorems of record, in the format of
[comparator](https://github.com/leanprover/comparator).  This
module imports `RS/Definitions.lean` — the self-contained statement
surface, whose only import is the Mathlib funnel — and states them
with `sorry`.  `Solution.lean` proves each by the
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

/-! ## 12. The theorems of record

Stated with `sorry`; `Solution.lean` proves each by the theorem of
record of the same name, and comparator certifies the match. -/

namespace Certified

open RS

/-- **The converse**: every mixed partition function is an
edge-rank-bounded parameter, with base `max 1 (k + 2ℓ)`. -/
theorem regts_sevenster_converse : RegtsSevensterConverseStatement :=
  sorry

/-- **The rank bound from a bounded mixed partition function.** -/
theorem edgeRankBounded_of_mixedBounded
    {f : ClosedFragment → ℂ} {B : ℕ}
    (hf : IsMixedPartitionFunctionBounded f B) :
    EdgeRankBounded f (max 1 (2 * B)) :=
  sorry

/-- **Deligne's theorem** on tensor categories: every essentially
small abelian ℂ-linear rigid symmetric monoidal category with
ℂ-bilinear tensor product, scalar unit endomorphisms, a finite
tensor generator and moderate growth of the lengths of its tensor
powers admits an exact faithful ℂ-linear symmetric monoidal fibre
functor to finite-dimensional super vector spaces. -/
theorem deligne_theorem : DeligneTheoremStatement.{1, 1} :=
  sorry

/-- **The forward direction**, with no hypothesis. -/
theorem regts_sevenster : RegtsSevensterStatement :=
  sorry

/-- **The quantitative forward direction**, with no hypothesis:
both dimensions at most `⌊2eR⌋`. -/
theorem regts_sevenster_quant : RegtsSevensterStatementQuant :=
  sorry

/-- **The characterisation**: a fragment parameter has bounded edge
rank exactly when it is a mixed partition function. -/
theorem regts_sevenster_characterisation
    (f : ClosedFragment → ℂ)
    (hempty : f emptyClosedFragment = 1)
    (hiso : ∀ W₁ W₂ : ClosedFragment, W₁.Equiv W₂ → f W₁ = f W₂) :
    (∃ R : ℕ, EdgeRankBounded f R) ↔ IsMixedPartitionFunction f :=
  sorry

/-- **The quantitative round trip**: edge rank `R` gives dimension
`⌊2eR⌋`, and dimension `B` gives edge rank base `max 1 (2B)`. -/
theorem regts_sevenster_quant_characterisation
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
