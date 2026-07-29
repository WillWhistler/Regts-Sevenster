import RS.Common.MathlibDeps

/-!
# Young diagram helpers

Shared Young-diagram vocabulary: the square diagram and the hook
membership predicate.  The hook `IsInHook a b μ` is the confinement
region of the alive shapes in the hook-confinement argument, and the
square diagram is the shape whose dimension growth drives that
confinement.
-/

namespace RS

/-- The `s × s` square Young diagram. -/
def squareDiagram (s : ℕ) : YoungDiagram :=
  YoungDiagram.ofRowLens (List.replicate s s) <| by
    intro i j _
    simp

/-- Membership in the `(a, b)` hook: every row after the first `a`
has length at most `b` (rows are indexed from `0`, so this reads
`rowLen a ≤ b` by antitonicity of row lengths). -/
def IsInHook (a b : ℕ) (μ : YoungDiagram) : Prop :=
  μ.rowLen a ≤ b

/-! ### Square diagram: row lengths and membership -/

/-- The row-length list of the `s × s` square diagram is `s` copies
of `s`. -/
theorem squareDiagram_rowLens (s : ℕ) :
    (squareDiagram s).rowLens = List.replicate s s :=
  YoungDiagram.rowLens_ofRowLens_eq_self (fun x hx => by
    rw [List.mem_replicate] at hx; omega)

/-- A cell `(i, j)` lies in the `s × s` square diagram precisely when
both coordinates are strictly below `s`. -/
@[simp]
theorem mem_squareDiagram {s : ℕ} {c : ℕ × ℕ} :
    c ∈ squareDiagram s ↔ c.1 < s ∧ c.2 < s := by
  simp only [squareDiagram, YoungDiagram.ofRowLens, YoungDiagram.mem_mk,
    YoungDiagram.mem_cellsOfRowLens, List.length_replicate,
      List.getElem_replicate]
  exact ⟨fun ⟨h1, h2⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨h1, h2⟩⟩

/-- The length of row `a` in the `s × s` square diagram is `s` when
`a < s`. -/
theorem rowLen_squareDiagram {s a : ℕ} (ha : a < s) :
    (squareDiagram s).rowLen a = s := by
  apply le_antisymm
  · -- rowLen a ≤ s: otherwise (a, s) ∈ squareDiagram s, giving s < s
    exact Nat.not_lt.mp fun h =>
      absurd (mem_squareDiagram.mp (YoungDiagram.mem_iff_lt_rowLen.mpr h)).2
        (lt_irrefl s)
  · -- s ≤ rowLen a: otherwise rowLen a < s and (a, rowLen a) ∈ squareDiagram s,
    -- giving rowLen a < rowLen a
    exact Nat.not_lt.mp fun h =>
      absurd (YoungDiagram.mem_iff_lt_rowLen.mp
        (mem_squareDiagram.mpr ⟨ha, h⟩)) (lt_irrefl _)

/-- The cardinality (number of cells) of the `s × s` square diagram
is `s²`. -/
theorem squareDiagram_card (s : ℕ) : (squareDiagram s).card = s ^ 2 := by
  have hext : (squareDiagram s).cells = Finset.range s ×ˢ Finset.range s := by
    ext c
    simp [Finset.mem_product, Finset.mem_range]
  simp [YoungDiagram.card, hext, Finset.card_product, sq]

/-! ### Square diagram containment -/

/-- If the `(s − 1)`-th row of `μ` has length at least `s`, the
`s × s` square fits inside `μ`. -/
theorem squareDiagram_le_of_rowLen {s : ℕ} {μ : YoungDiagram}
    (h : s ≤ μ.rowLen (s - 1)) : squareDiagram s ≤ μ := by
  intro c hc
  rw [mem_squareDiagram] at hc
  rw [YoungDiagram.mem_iff_lt_rowLen]
  rcases s with _ | s
  · exact absurd hc.1 (by omega)
  · simp only [Nat.succ_sub_one] at h
    calc c.2 < s + 1 := hc.2
      _ ≤ μ.rowLen s := h
      _ ≤ μ.rowLen c.1 := μ.rowLen_anti c.1 s (by omega)

/-! ### Hook predicate -/

/-- The negation of the hook predicate is equivalent to the cell
`(a, b)` belonging to the diagram. -/
theorem not_isInHook_iff {a b : ℕ} {μ : YoungDiagram} :
    ¬IsInHook a b μ ↔ b < μ.rowLen a :=
  Nat.not_le

/-! ### List-to-diagram bridge -/

/-- The row length of the diagram built from `w` at index `i` equals
`w.getD i 0`: the `i`-th entry when `i` is in range, and `0`
otherwise. -/
theorem rowLen_ofRowLens_getD {w : List ℕ} {hw : w.SortedGE} (i : ℕ) :
    (YoungDiagram.ofRowLens w hw).rowLen i = w.getD i 0 := by
  rw [List.getD_eq_getElem?_getD]
  by_cases hi : i < w.length
  · rw [List.getElem?_eq_getElem hi, Option.getD_some]
    exact YoungDiagram.rowLen_ofRowLens ⟨i, hi⟩
  · rw [List.getElem?_eq_none (by omega), Option.getD_none]
    have : ¬(0 < (YoungDiagram.ofRowLens w hw).rowLen i) := by
      rw [← YoungDiagram.mem_iff_lt_rowLen, YoungDiagram.mem_ofRowLens]
      exact fun ⟨h, _⟩ => absurd h (not_lt.mpr (by omega))
    omega

end RS
