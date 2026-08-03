import RS.TheoremConverse
import RS.Classical.Deligne.DeligneAssembly

/-!
# The theorems, unconditionally

The theorems of record, carrying no hypothesis: Deligne's theorem,
in fibre-functor form, is `RS.deligne_theorem`
(`RS/Classical/Deligne/DeligneAssembly.lean`),
so the forms in `RS/TheoremForward.lean`, `RS/TheoremQuant.lean` and
`RS/TheoremConverse.lean` that take it as an argument are applied to
it here.  Those forms remain available alongside: they exhibit the
dependency structure, which is what a reader checking the argument
against the literature wants.

The axiom checks are pinned in
`RS/Assembly/BlueprintDeligne.lean`.
-/

namespace RS

/-- **The Regts–Sevenster theorem**: every graph parameter with
exponentially bounded edge-connection rank is a mixed partition
function. -/
theorem regts_sevenster : RegtsSevensterStatement :=
  regts_sevenster_deligne_only deligne_theorem

/-- **The Regts–Sevenster theorem, quantitative form**. -/
theorem regts_sevenster_quant : RegtsSevensterStatementQuant :=
  regts_sevenster_quant_deligne_only deligne_theorem

/-- **The characterisation**: for a normalised isomorphism-invariant
parameter, bounded edge-connection rank and being a mixed partition
function are equivalent. -/
theorem regts_sevenster_characterisation (f : ClosedFragment → ℂ)
    (hempty : f emptyClosedFragment = 1)
    (hiso : ∀ W₁ W₂ : ClosedFragment, W₁.Equiv W₂ → f W₁ = f W₂) :
    (∃ R : ℕ, EdgeRankBounded f R) ↔ IsMixedPartitionFunction f :=
  regts_sevenster_iff deligne_theorem f hempty hiso

/-- **The quantitative round trip**. -/
theorem regts_sevenster_quant_characterisation
    (f : ClosedFragment → ℂ)
    (hempty : f emptyClosedFragment = 1)
    (hiso : ∀ W₁ W₂ : ClosedFragment, W₁.Equiv W₂ → f W₁ = f W₂) :
    (∀ R, EdgeRankBounded f R →
      IsMixedPartitionFunctionBounded f
        ⌊2 * Real.exp 1 * (R : ℝ)⌋₊) ∧
    (∀ B, IsMixedPartitionFunctionBounded f B →
      EdgeRankBounded f (max 1 (2 * B))) :=
  regts_sevenster_quant_roundtrip deligne_theorem f hempty hiso

end RS
