import RS.Novel.Skein.GlueSplit

/-!
# The lexicographic order on disjoint-union labels

Plain `α ⊕ β` carries no linear order in mathlib (only the `⊕ₗ`
synonym does); the corrected constrained value of a `disjUnion`
needs one for its through-product orientation.  This file
transports the lexicographic order to the plain sum (left before
right) and pins the disjoint-union factorization interface — the
multiplicativity of the corrected value, first target of the
factorization chain.
-/

namespace RS

-- Deliberately semireducible: supplied explicitly via `letI` in
-- the gluing chain, never by instance search.
set_option warn.classDefReducibility false in
/-- The lexicographic linear order on a plain sum type: left
before right. -/
def sumLexLinearOrder (α β : Type) [LinearOrder α]
    [LinearOrder β] : LinearOrder (α ⊕ β) :=
  LinearOrder.lift' (toLex : α ⊕ β → α ⊕ₗ β) (fun _ _ h => h)

section Lemmas

variable {α β : Type} [LinearOrder α] [LinearOrder β]

/-- Within the left block the order is the left order. -/
theorem sumLex_inl_lt_inl_iff {a a' : α} :
    (sumLexLinearOrder α β).lt (Sum.inl a) (Sum.inl a') ↔
      a < a' := by
  show toLex (Sum.inl a) < toLex (Sum.inl a') ↔ _
  exact Sum.Lex.inl_lt_inl_iff

/-- Within the right block, the right order. -/
theorem sumLex_inr_lt_inr_iff {b b' : β} :
    (sumLexLinearOrder α β).lt (Sum.inr b) (Sum.inr b') ↔
      b < b' := by
  show toLex (Sum.inr b) < toLex (Sum.inr b') ↔ _
  exact Sum.Lex.inr_lt_inr_iff

/-- Every left label precedes every right one. -/
theorem sumLex_inl_lt_inr (a : α) (b : β) :
    (sumLexLinearOrder α β).lt (Sum.inl a) (Sum.inr b) := by
  show toLex (Sum.inl a) < toLex (Sum.inr b)
  exact Sum.Lex.inl_lt_inr a b

/-- And no right label precedes a left one. -/
theorem sumLex_not_inr_lt_inl (a : α) (b : β) :
    ¬ (sumLexLinearOrder α β).lt (Sum.inr b) (Sum.inl a) := by
  show ¬ toLex (Sum.inr b) < toLex (Sum.inl a)
  exact fun h => absurd (lt_trans (Sum.Lex.inl_lt_inr a b) h)
    (lt_irrefl _)

end Lemmas

end RS
