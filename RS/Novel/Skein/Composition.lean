import RS.Novel.Skein.FlagGraph

/-!
# Fragment composition

Composition of fragments by interface gluing: an `(s + t)`-fragment
and a `(t + u)`-fragment compose to an `(s + u)`-fragment by gluing
the last `t` boundary labels of the first to the first `t` of the
second, in order.  The gluing is the iterated single-pair primitive
of `FlagGraph.lean`: `glueInterface` recurses on `t`, gluing the
top interface pair and re-indexing the surviving labels.

The re-indexing is built from one-point removals, and the value
computations for those removals sit here beside them: the gluing
chain rewrites boundary states through the re-indexings, so it
needs each surviving label's new index as an explicit natural
number.
-/

namespace RS

/-! ### Removing a point -/

/-- Removing one point from `Fin (n + 1)` leaves `Fin n`. -/
noncomputable def finRemoveEquiv {n : ℕ} (a : Fin (n + 1)) :
    {x : Fin (n + 1) // x ≠ a} ≃ Fin n where
  toFun x := ((finSuccEquiv' a) x.val).get (by
    rw [Option.isSome_iff_ne_none]
    intro h
    exact x.prop ((finSuccEquiv' a).injective (h.trans (finSuccEquiv'_at
      a).symm)))
  invFun y := ⟨(finSuccEquiv' a).symm (some y), by
    intro h
    have happ := (finSuccEquiv' a).apply_symm_apply (some y)
    rw [h, finSuccEquiv'_at] at happ
    exact Option.some_ne_none y happ.symm⟩
  left_inv x := Subtype.ext (by simp)
  right_inv y := by simp

/-- Removing `inl a` and `inr b` from a sum splits into the two
one-point removals. -/
def sumRemoveSplitEquiv {A B : Type} (a : A) (b : B) :
    {x : A ⊕ B // x ≠ Sum.inl a ∧ x ≠ Sum.inr b} ≃
      {x : A // x ≠ a} ⊕ {y : B // y ≠ b} where
  toFun := fun
    | ⟨Sum.inl v, h⟩ => Sum.inl ⟨v, fun he => h.1 (congrArg Sum.inl he)⟩
    | ⟨Sum.inr w, h⟩ => Sum.inr ⟨w, fun he => h.2 (congrArg Sum.inr he)⟩
  invFun := fun
    | Sum.inl v => ⟨Sum.inl v.val,
        fun h => v.prop (Sum.inl.inj h), fun h => Sum.inl_ne_inr h⟩
    | Sum.inr w => ⟨Sum.inr w.val,
        fun h => Sum.inr_ne_inl h, fun h => w.prop (Sum.inr.inj h)⟩
  left_inv := fun
    | ⟨Sum.inl _, _⟩ => rfl
    | ⟨Sum.inr _, _⟩ => rfl
  right_inv := fun
    | Sum.inl _ => rfl
    | Sum.inr _ => rfl

/-- Removing label `t` from `Fin (t + 1 + u)` leaves `Fin (t + u)`. -/
noncomputable def rightRemoveEquiv (t u : ℕ) :
    {x : Fin (t + 1 + u) // x ≠ ⟨t, by omega⟩} ≃ Fin (t + u) :=
  Equiv.trans
    (Equiv.subtypeEquiv (finCongr (by omega : t + 1 + u = (t + u) + 1))
      (fun x => by simp [Fin.ext_iff]))
    (finRemoveEquiv ⟨t, by omega⟩)

/-- The label re-indexing after gluing the top interface pair:
removing the last label on the left and label `t` on the right. -/
noncomputable def interfaceStepEquiv (s t u : ℕ) :
    {x : Fin (s + t + 1) ⊕ Fin (t + 1 + u) //
      x ≠ Sum.inl ⟨s + t, Nat.lt_succ_self _⟩ ∧
      x ≠ Sum.inr ⟨t, by omega⟩} ≃ Fin (s + t) ⊕ Fin (t + u) :=
  Equiv.trans (sumRemoveSplitEquiv _ _)
    (Equiv.sumCongr (finRemoveEquiv _) (rightRemoveEquiv t u))

/-! ### Value computation for the one-point removals

A removal is inverted by `Fin.succAbove`, which shifts the indices
at or above the removed point up by one.  Reading that off gives
each surviving label's new index as an explicit natural number. -/

/-- `Fin.succAbove` shifts the indices at or above `a` up by one. -/
private theorem succAbove_val_ite {n : ℕ} (a : Fin (n + 1)) (y : Fin n) :
    ((a.succAbove y : Fin (n + 1)) : ℕ) =
      if (y : ℕ) < (a : ℕ) then (y : ℕ) else (y : ℕ) + 1 := by
  by_cases hc : Fin.castSucc y < a
  · rw [Fin.succAbove_of_castSucc_lt _ _ hc]
    have h1 : (y : ℕ) < (a : ℕ) := hc
    rw [if_pos h1]
    rfl
  · have hc' : a ≤ Fin.castSucc y := not_lt.mp hc
    rw [Fin.succAbove_of_le_castSucc _ _ hc']
    have h1 : (a : ℕ) ≤ (y : ℕ) := hc'
    rw [if_neg (not_lt.mpr h1)]
    rfl

/-- Inverting that shift: a label above the removed point drops by
one, a label below it keeps its index. -/
private theorem removed_val_ite {n : ℕ} {a : Fin (n + 1)} {y : Fin n}
    {v : ℕ} (h : ((a.succAbove y : Fin (n + 1)) : ℕ) = v) :
    (y : ℕ) = if v < (a : ℕ) then v else v - 1 := by
  rw [succAbove_val_ite] at h
  by_cases hc : (y : ℕ) < (a : ℕ)
  · rw [if_pos hc] at h
    rw [if_pos (by omega)]
    omega
  · rw [if_neg hc] at h
    rw [if_neg (by omega)]
    omega

/-- `Fin.succAbove` at the removed point inverts `finRemoveEquiv`. -/
theorem finRemoveEquiv_apply_val {n : ℕ} (a : Fin (n + 1))
    (x : {x : Fin (n + 1) // x ≠ a}) :
    a.succAbove (finRemoveEquiv a x) = x.val :=
  congrArg Subtype.val ((finRemoveEquiv a).symm_apply_apply x)

/-- The index a surviving label takes after a one-point removal. -/
theorem finRemoveEquiv_val {n : ℕ} (a : Fin (n + 1))
    (x : {x : Fin (n + 1) // x ≠ a}) :
    (finRemoveEquiv a x : ℕ) =
      if (x.val : ℕ) < (a : ℕ) then (x.val : ℕ) else (x.val : ℕ) - 1 :=
  removed_val_ite (congrArg Fin.val (finRemoveEquiv_apply_val a x))

/-- Removing the top point leaves every surviving label's index
unchanged. -/
theorem finRemoveEquiv_top_val {n : ℕ}
    (x : {x : Fin (n + 1) // x ≠ ⟨n, Nat.lt_succ_self n⟩}) :
    (finRemoveEquiv ⟨n, Nat.lt_succ_self n⟩ x : ℕ) = (x.val : ℕ) := by
  have h := finRemoveEquiv_val ⟨n, Nat.lt_succ_self n⟩ x
  have hx : (x.val : ℕ) ≠ n := fun hh => x.prop (Fin.ext hh)
  have hb : (x.val : ℕ) < n + 1 := x.val.isLt
  have ha : ((⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) : ℕ) = n := rfl
  rw [h, ha, if_pos (by omega)]

/-- `Fin.succAbove` at `t` inverts `rightRemoveEquiv`. -/
theorem rightRemoveEquiv_apply_val (t u : ℕ)
    (x : {x : Fin (t + 1 + u) // x ≠ ⟨t, by omega⟩}) :
    (((⟨t, by omega⟩ : Fin (t + u + 1)).succAbove
        (rightRemoveEquiv t u x) : Fin (t + u + 1)) : ℕ) =
      (x.val : ℕ) :=
  congrArg (fun z : {x : Fin (t + 1 + u) // x ≠ ⟨t, by omega⟩} =>
      (z.val : ℕ))
    ((rightRemoveEquiv t u).symm_apply_apply x)

/-- The index a surviving label takes after removing label `t` on
the right. -/
theorem rightRemoveEquiv_val (t u : ℕ)
    (x : {x : Fin (t + 1 + u) // x ≠ ⟨t, by omega⟩}) :
    (rightRemoveEquiv t u x : ℕ) =
      if (x.val : ℕ) < t then (x.val : ℕ) else (x.val : ℕ) - 1 :=
  removed_val_ite (rightRemoveEquiv_apply_val t u x)

/-! ### Gluing an interface -/

/-- Glue the `t` interface labels of a fragment over
`Fin (s + t) ⊕ Fin (t + u)`: the pairs `(inl (s + k), inr k)` for
`k < t`, glued top pair first. -/
noncomputable def glueInterface (s : ℕ) :
    (t : ℕ) → (u : ℕ) → Fragment (Fin (s + t) ⊕ Fin (t + u)) →
      Fragment (Fin s ⊕ Fin u)
  | 0, _, W => W.relabel
      (Equiv.sumCongr (finCongr (by omega)) (finCongr (by omega)))
  | t + 1, u, W =>
      let W' := W.gluePair (Sum.inl ⟨s + t, by omega⟩)
        (Sum.inr ⟨t, by omega⟩) (by simp)
      glueInterface s t u (W'.relabel (interfaceStepEquiv s t u))

/-- Composition of fragments: glue the last `t` labels of `F` to the
first `t` labels of `G`, in order. -/
noncomputable def Fragment.compose {s t u : ℕ}
    (F : Fragment (Fin (s + t))) (G : Fragment (Fin (t + u))) :
    Fragment (Fin (s + u)) :=
  (glueInterface s t u (F.disjUnion G)).relabel finSumFinEquiv

end RS
