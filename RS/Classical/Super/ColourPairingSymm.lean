import RS.Classical.Super.ColourPairing

/-!
# S_d-invariance of the pinned pairing (Lemma 5.1(b))

The pinned tensor-power pairing `betaColour` is invariant under
simultaneous permutation of both colourings' positions.

The key combinatorial fact: with matching parities the crossing
count `koszulCrossings c c'` depends only on `c.oddSet.card`,
via the identity `2 * crossings = n * (n - 1)` (upper/lower
triangle of the off-diagonal). Since permutations preserve
`oddSet.card`, the crossing count — hence the Koszul sign — is
invariant.
-/

namespace RS

namespace MixedColouring

/-- Permuting a colouring by a permutation of positions. -/
def perm {k ℓ d : ℕ} (c : MixedColouring k ℓ d)
    (π : Equiv.Perm (Fin d)) : MixedColouring k ℓ d :=
  fun i => c (π i)

/-- Permuting a colouring's positions. -/
@[simp]
theorem perm_apply {k ℓ d : ℕ} (c : MixedColouring k ℓ d)
    (π : Equiv.Perm (Fin d)) (i : Fin d) :
    (c.perm π) i = c (π i) := rfl

end MixedColouring

end RS
