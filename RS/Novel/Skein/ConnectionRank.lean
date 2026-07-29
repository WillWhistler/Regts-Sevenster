import RS.Common.RowSpanRank
import RS.Novel.Skein.FragmentEquiv

/-!
# Connection pairings and the edge-rank hypothesis

The hypothesis class of the main theorem, phrased on the flag
model: a graph parameter is a function on closed fragments (with
isomorphism invariance carried as a hypothesis where needed), its
connection pairing at arity `t` composes a `(0 + t)`-fragment with
a `(t + 0)`-fragment, and the edge-rank hypothesis bounds the rank
of the pairing by `R ^ t`.

Ranks of infinite matrices are avoided: the pairing is curried into
a linear map `Θ` from the free module on fragments to the function
space, and the rank condition bounds the `Module.rank` of its
range.  The literature instead reads the rank of the connection
matrix as the supremum of the ranks of its finite submatrices, and
`edgeRankBounded_iff_submatrixRank` proves the two readings the same
condition.

The base is an arbitrary natural number, where the literature takes
`R ≥ 1`.  Nothing is gained or lost by that: the bound weakens as the
base grows (`EdgeRankBounded.mono`), so a parameter admitted at
`R = 0` is admitted at `R = 1` already.
-/

namespace RS

/-- A closed fragment: no boundary labels. -/
abbrev ClosedFragment : Type 1 := Fragment (Fin 0)

/-- The full closure of two `t`-fragments: compose them as a
`(0 + t)`- and a `(t + 0)`-fragment. -/
noncomputable def pairClose {t : ℕ} (F G : Fragment (Fin t)) :
    ClosedFragment :=
  (F.relabel (finCongr (by omega : t = 0 + t))).compose
    (G.relabel (finCongr (by omega : t = t + 0)))

/-- The connection pairing of a parameter at arity `t`. -/
noncomputable def connectionPairing (f : ClosedFragment → ℂ) (t : ℕ)
    (F G : Fragment (Fin t)) : ℂ :=
  f (pairClose F G)

/-- The curried connection pairing as a linear map from the free
module on `t`-fragments to the function space. -/
noncomputable def connectionMap (f : ClosedFragment → ℂ) (t : ℕ) :
    (Fragment (Fin t) →₀ ℂ) →ₗ[ℂ] (Fragment (Fin t) → ℂ) :=
  Finsupp.lift _ ℂ _ (fun F G => connectionPairing f t F G)

/-- The edge-rank hypothesis `H2`: the connection pairing at every
arity has rank at most `R ^ t`. -/
def EdgeRankBounded (f : ClosedFragment → ℂ) (R : ℕ) : Prop :=
  ∀ t : ℕ, Module.rank ℂ (LinearMap.range (connectionMap f t)) ≤
    (R : Cardinal) ^ t

/-- Edge-rank boundedness is monotone in the base. -/
theorem EdgeRankBounded.mono {f : ClosedFragment → ℂ} {R R' : ℕ}
    (hf : EdgeRankBounded f R) (hRR : R ≤ R') :
    EdgeRankBounded f R' := fun t =>
  le_trans (hf t) (Cardinal.power_le_power_right
    (by exact_mod_cast hRR))

/-- The rank condition as the literature states it, at arity `t`:
every finite submatrix of the connection matrix — a finite set `S` of
row fragments against a finite set `T` of column fragments — has rank
at most `n`. -/
def SubmatrixRankBounded (f : ClosedFragment → ℂ) (t n : ℕ) : Prop :=
  ∀ S T : Finset (Fragment (Fin t)),
    (submatrixOn (connectionPairing f t) S T).rank ≤ n

/-- **The two readings of the connection rank agree.**  Bounding the
dimension of the row span of the connection pairing, as
`EdgeRankBounded` does, is the same condition as bounding the ranks of
all the finite submatrices of the connection matrix, which is how the
rank of that infinite matrix is defined in the literature. -/
theorem edgeRankBounded_iff_submatrixRank (f : ClosedFragment → ℂ)
    (R : ℕ) :
    EdgeRankBounded f R ↔ ∀ t : ℕ, SubmatrixRankBounded f t (R ^ t) := by
  refine forall_congr' fun t => ?_
  have h := rank_range_lift_le_iff (connectionPairing f t) (R ^ t)
  rw [Nat.cast_pow] at h
  exact h

/-- The empty closed fragment. -/
noncomputable def emptyClosedFragment : ClosedFragment :=
  (Fragment.circlesOnly 0).relabel (Equiv.equivOfIsEmpty Empty (Fin 0))

/-- The hypothesis class of the main theorem: a parameter on closed
fragments, normalized on the empty graph, with exponentially
bounded connection rank. -/
structure EdgeRankParameter (R : ℕ) where
  /-- The parameter, on concrete closed fragments. -/
  val : ClosedFragment → ℂ
  /-- The parameter takes the value `1` on the empty graph. -/
  val_empty : val emptyClosedFragment = 1
  /-- The parameter is invariant under fragment isomorphism. -/
  iso_invariant : ∀ W₁ W₂ : ClosedFragment, W₁.Equiv W₂ → val W₁ = val W₂
  /-- The rank bound. -/
  rank_bounded : EdgeRankBounded val R

end RS
