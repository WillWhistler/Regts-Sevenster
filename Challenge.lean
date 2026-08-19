import Mathlib

/-!
# The certification challenge

The trusted half of an independently checkable certificate for the
theorems of record, in the format of
[comparator](https://github.com/leanprover/comparator).  This module
is self-contained: it imports Mathlib and nothing else, carries the
whole statement surface the theorems are phrased in, and states them
with `sorry`.  `Solution.lean` proves each by the theorem of record
of the same name, against the identical definitions carried by
`RS/Definitions.lean`.

Comparator builds this module and `Solution.lean` separately, exports
both environments at the kernel level, and checks that each theorem
below is proved in the solution with an identical statement, about
identical definitions; that the proofs use no axiom outside
`[propext, Classical.choice, Quot.sound]`
(`comparator-config.json`); and that the kernel replays them.
Reading this file — against Mathlib alone — therefore determines
exactly what is being certified.

The sections below are the flag model of multigraph fragments with
its gluing, fragment isomorphism, composition, the connection
pairing and the edge-rank hypothesis, Eulerian edge subsets, the
mixed partition function (Regts–Sevenster's Definition 5), and the
named statements.

This module deliberately contains `sorry` — that is the challenge
format — so it is not part of the default build target.
-/


namespace RS

/-! ## 1. Inversions and the sorting sign

The sorting sign supplies the
antisymmetry of the odd-colour evaluation in Definition 5: reordering
the odd colours multiplies the vertex value by the sign of the
permutation, realized as `(−1)` to the inversion count. -/

/-- The number of inversions of a list over a linear order. -/
def inversions {α : Type} [LinearOrder α] : List α → ℕ
  | [] => 0
  | a :: l => (l.filter (fun b => b < a)).length + inversions l

/-- The sorting sign of a list: `(−1)` to the number of
inversions. -/
def sortSign {α : Type} [LinearOrder α] (l : List α) : ℤ :=
  (-1) ^ inversions l

/-! ## 2. The flag model of multigraph fragments

A *fragment* is a finite
multigraph in half-edge (flag) form: flags attach to internal
vertices or to boundary labels, a fixed-point-free involution pairs
flags into edges, each boundary label carries exactly one flag, and
free circles are counted separately.  Gluing two boundary labels
either closes an edge into a free circle (when the two flags bound a
common edge) or rewires the two edges end to end.  These are the
graphs the main theorems quantify over; `ClosedFragment` below is
the case of no boundary labels. -/

/-- A fragment over the boundary-label type `α`: a finite multigraph
in half-edge (flag) form whose dangling flags are labelled
bijectively by `α`, together with a count of free circles. -/
structure Fragment (α : Type) where
  /-- The type of flags (half-edges). -/
  Flag : Type
  /-- The type of internal vertices. -/
  Vertex : Type
  /-- Flags form a finite type with decidable equality. -/
  [flagFintype : Fintype Flag]
  [flagDecEq : DecidableEq Flag]
  /-- Vertices form a finite type. -/
  [vertexFintype : Fintype Vertex]
  /-- Each flag is attached to an internal vertex or to a boundary
  label. -/
  attach : Flag → Vertex ⊕ α
  /-- The edge involution: every flag has a partner. -/
  pairing : Flag → Flag
  /-- The pairing is an involution. -/
  pairing_invol : ∀ f, pairing (pairing f) = f
  /-- The pairing has no fixed points. -/
  pairing_ne : ∀ f, pairing f ≠ f
  /-- The flag at each boundary label. -/
  boundaryFlag : α → Flag
  /-- The boundary flag of `ℓ` is attached to `ℓ`. -/
  attach_boundaryFlag : ∀ ℓ, attach (boundaryFlag ℓ) = Sum.inr ℓ
  /-- Any flag attached to `ℓ` is the boundary flag of `ℓ`. -/
  eq_boundaryFlag : ∀ ℓ f, attach f = Sum.inr ℓ → f = boundaryFlag ℓ
  /-- Free circles, counted separately. -/
  circles : ℕ

attribute [instance] Fragment.flagFintype Fragment.flagDecEq
  Fragment.vertexFintype

namespace Fragment

variable {α β : Type}

/-- Boundary flags of distinct labels are distinct. -/
theorem boundaryFlag_injective (W : Fragment α) :
    Function.Injective W.boundaryFlag := by
  intro i j hij
  have hi := W.attach_boundaryFlag i
  have hj := W.attach_boundaryFlag j
  rw [hij, hj] at hi
  exact (Sum.inr.inj hi).symm

/-- The partner of a boundary flag is not that boundary flag's own
label's flag; more useful below: the partner of the flag at `i` is
the flag at `j` precisely when the flag at `j`'s partner is the flag
at `i`. -/
theorem pairing_boundaryFlag_comm (W : Fragment α) {i j : α}
    (h : W.pairing (W.boundaryFlag i) = W.boundaryFlag j) :
    W.pairing (W.boundaryFlag j) = W.boundaryFlag i := by
  rw [← h, W.pairing_invol]

/-- The closed fragment with no flags, no vertices, and a given
number of free circles. -/
def circlesOnly (c : ℕ) : Fragment Empty where
  Flag := Empty
  Vertex := Empty
  attach := Empty.elim
  pairing := Empty.elim
  pairing_invol := fun f => f.elim
  pairing_ne := fun f => f.elim
  boundaryFlag := Empty.elim
  attach_boundaryFlag := fun ℓ => ℓ.elim
  eq_boundaryFlag := fun ℓ => ℓ.elim
  circles := c

/-- Transport a fragment along an equivalence of label types. -/
def relabel (W : Fragment α) (e : α ≃ β) : Fragment β where
  Flag := W.Flag
  Vertex := W.Vertex
  attach := fun f => (W.attach f).map id e
  pairing := W.pairing
  pairing_invol := W.pairing_invol
  pairing_ne := W.pairing_ne
  boundaryFlag := fun ℓ => W.boundaryFlag (e.symm ℓ)
  attach_boundaryFlag := fun ℓ => by
    simp [W.attach_boundaryFlag (e.symm ℓ)]
  eq_boundaryFlag := fun ℓ f h => by
    rcases ha : W.attach f with v | ℓ'
    · simp [ha] at h
    · simp only [ha, Sum.map_inr] at h
      obtain rfl : e ℓ' = ℓ := Sum.inr.inj h
      rw [Equiv.symm_apply_apply]
      exact W.eq_boundaryFlag ℓ' f ha
  circles := W.circles

/-- Disjoint union of fragments, over the sum of the label types. -/
def disjUnion (W₁ : Fragment α) (W₂ : Fragment β) :
    Fragment (α ⊕ β) where
  Flag := W₁.Flag ⊕ W₂.Flag
  Vertex := W₁.Vertex ⊕ W₂.Vertex
  attach := Sum.elim
    (fun f => (W₁.attach f).map Sum.inl Sum.inl)
    (fun f => (W₂.attach f).map Sum.inr Sum.inr)
  pairing := Sum.map W₁.pairing W₂.pairing
  pairing_invol := fun f => by
    cases f <;> simp [W₁.pairing_invol, W₂.pairing_invol]
  pairing_ne := fun f => by
    cases f with
    | inl g => simpa using fun h => W₁.pairing_ne g h
    | inr g => simpa using fun h => W₂.pairing_ne g h
  boundaryFlag := Sum.elim
    (fun ℓ => Sum.inl (W₁.boundaryFlag ℓ))
    (fun ℓ => Sum.inr (W₂.boundaryFlag ℓ))
  attach_boundaryFlag := fun ℓ => by
    cases ℓ <;> simp [W₁.attach_boundaryFlag, W₂.attach_boundaryFlag]
  eq_boundaryFlag := fun ℓ f h => by
    cases ℓ with
    | inl ℓ₁ =>
      cases f with
      | inl g =>
        rcases ha : W₁.attach g with v | ℓ' <;> simp [ha] at h
        subst h
        simp [W₁.eq_boundaryFlag ℓ' g ha]
      | inr g =>
        rcases ha : W₂.attach g with v | ℓ' <;> simp [ha] at h
    | inr ℓ₂ =>
      cases f with
      | inl g =>
        rcases ha : W₁.attach g with v | ℓ' <;> simp [ha] at h
      | inr g =>
        rcases ha : W₂.attach g with v | ℓ' <;> simp [ha] at h
        subst h
        simp [W₂.eq_boundaryFlag ℓ' g ha]
  circles := W₁.circles + W₂.circles

/-! ### Single-pair gluing -/

section GluePair

/-- The labels surviving a glue at `{i, j}`. -/
abbrev SurvivingLabel (α : Type) (i j : α) : Type :=
  {x : α // x ≠ i ∧ x ≠ j}

/-- The flags surviving a glue at `{i, j}`: all but the two glued
boundary flags. -/
abbrev SurvivingFlag (W : Fragment α) (i j : α) : Type :=
  {f : W.Flag // f ≠ W.boundaryFlag i ∧ f ≠ W.boundaryFlag j}

/-- A surviving flag is never attached to a glued label. -/
theorem survivingFlag_attach_ne {W : Fragment α} {i j : α}
    (f : SurvivingFlag W i j) :
    W.attach f.val ≠ Sum.inr i ∧ W.attach f.val ≠ Sum.inr j :=
  ⟨fun h => f.prop.1 (W.eq_boundaryFlag i f.val h),
   fun h => f.prop.2 (W.eq_boundaryFlag j f.val h)⟩

/-- The attachment map after gluing at `{i, j}`: unchanged, with the
label type restricted to the surviving labels. -/
def glueAttach (W : Fragment α) (i j : α) (f : SurvivingFlag W i j) :
    W.Vertex ⊕ SurvivingLabel α i j :=
  match ha : W.attach f.val with
  | Sum.inl v => Sum.inl v
  | Sum.inr ℓ => Sum.inr ⟨ℓ,
      fun h => (survivingFlag_attach_ne f).1 (h ▸ ha),
      fun h => (survivingFlag_attach_ne f).2 (h ▸ ha)⟩

/-- `glueAttach` agrees with `attach` under the label inclusion. -/
theorem glueAttach_spec (W : Fragment α) (i j : α)
    (f : SurvivingFlag W i j) :
    (glueAttach W i j f).map id Subtype.val = W.attach f.val := by
  unfold glueAttach
  split <;> simp_all

end GluePair

section GluePairRewire

variable {W : Fragment α} {i j : α}

/-- The rewired pairing for an *open* glue (the two glued flags do
not bound a common edge): the far ends of the two glued edges become
partners; all other flags keep their partners. -/
def rewire (hopen : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag j)
    (f : SurvivingFlag W i j) : SurvivingFlag W i j :=
  if hfi : W.pairing f.val = W.boundaryFlag i then
    ⟨W.pairing (W.boundaryFlag j),
      fun h => hopen (W.pairing_boundaryFlag_comm h),
      fun h => W.pairing_ne (W.boundaryFlag j) h⟩
  else if hfj : W.pairing f.val = W.boundaryFlag j then
    ⟨W.pairing (W.boundaryFlag i),
      fun h => W.pairing_ne (W.boundaryFlag i) h,
      fun h => hopen h⟩
  else
    ⟨W.pairing f.val, hfi, hfj⟩

/-- Rewiring across an open glue is an involution: it is the glued
fragment's edge pairing. -/
theorem rewire_invol (hij : i ≠ j)
    (hopen : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag j)
    (f : SurvivingFlag W i j) :
    rewire hopen (rewire hopen f) = f := by
  have hbne : W.boundaryFlag i ≠ W.boundaryFlag j :=
    fun h => hij (W.boundaryFlag_injective h)
  unfold rewire
  split
  · -- f is the far end of i's edge; its rewired partner is the far
    -- end of j's edge, whose rewired partner is back at f.
    rename_i hfi
    rw [dif_neg (by
      rw [W.pairing_invol]
      exact fun h => hbne h.symm)]
    rw [dif_pos (by rw [W.pairing_invol])]
    refine Subtype.ext ?_
    have h2 := congrArg W.pairing hfi
    rw [W.pairing_invol] at h2
    exact h2.symm
  · split
    · rename_i hfi hfj
      rw [dif_pos (by rw [W.pairing_invol])]
      refine Subtype.ext ?_
      have h2 := congrArg W.pairing hfj
      rw [W.pairing_invol] at h2
      exact h2.symm
    · rename_i hfi hfj
      rw [dif_neg (by rw [W.pairing_invol]; exact fun h => f.prop.1 h)]
      rw [dif_neg (by rw [W.pairing_invol]; exact fun h => f.prop.2 h)]
      exact Subtype.ext (W.pairing_invol f.val)

/-- And fixed-point-free, so the glued fragment is again a
fragment. -/
theorem rewire_ne (hij : i ≠ j)
    (hopen : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag j)
    (f : SurvivingFlag W i j) : rewire hopen f ≠ f := by
  have hbne : W.boundaryFlag i ≠ W.boundaryFlag j :=
    fun h => hij (W.boundaryFlag_injective h)
  unfold rewire
  split
  · rename_i hfi
    intro h
    have hval := congrArg Subtype.val h
    have : W.pairing f.val = W.boundaryFlag j := by
      rw [← hval, W.pairing_invol]
    exact hbne (hfi ▸ this)
  · split
    · rename_i hfi hfj
      intro h
      have hval := congrArg Subtype.val h
      exact hfi (by rw [← hval, W.pairing_invol])
    · intro h
      exact W.pairing_ne f.val (congrArg Subtype.val h)

end GluePairRewire

/-! ### The glued fragment -/

section Glue

variable (W : Fragment α) (i j : α)

/-- The boundary flag of a surviving label survives the glue. -/
def glueBoundaryFlag (ℓ : SurvivingLabel α i j) : SurvivingFlag W i j :=
  ⟨W.boundaryFlag ℓ.val,
    fun h => ℓ.prop.1 (W.boundaryFlag_injective h),
    fun h => ℓ.prop.2 (W.boundaryFlag_injective h)⟩

variable {W i j}

/-- The glued attachment lands on a surviving label exactly when
the original attachment lands on its underlying label. -/
theorem glueAttach_inr {f : SurvivingFlag W i j}
    {ℓ : SurvivingLabel α i j} :
    glueAttach W i j f = Sum.inr ℓ ↔ W.attach f.val = Sum.inr ℓ.val := by
  constructor
  · intro h
    have := glueAttach_spec W i j f
    rw [h] at this
    simpa using this.symm
  · intro h
    unfold glueAttach
    split
    · simp_all
    · rename_i ℓ' ha
      rw [ha] at h
      exact congrArg Sum.inr (Subtype.ext (Sum.inr.inj h))

variable (W i j)

/-- The glued attachment of a surviving label's flag is that
label. -/
theorem glue_attach_boundaryFlag (ℓ : SurvivingLabel α i j) :
    glueAttach W i j (glueBoundaryFlag W i j ℓ) = Sum.inr ℓ :=
  glueAttach_inr.mpr (W.attach_boundaryFlag ℓ.val)

/-- A surviving flag attached to a surviving label is that label's
boundary flag. -/
theorem glue_eq_boundaryFlag (ℓ : SurvivingLabel α i j)
    (f : SurvivingFlag W i j) (h : glueAttach W i j f = Sum.inr ℓ) :
    f = glueBoundaryFlag W i j ℓ :=
  Subtype.ext (W.eq_boundaryFlag ℓ.val f.val (glueAttach_inr.mp h))

/-- A glue at `{i, j}` with a prescribed pairing and circle count.

Flags, vertices, attachment and boundary flags of a single-pair glue
are determined by `W` alone; only the pairing and the circle count
tell the closed and open glues apart.  Naming that common part gives
the two glues a single shape, so any fact about a glue that does not
mention its pairing is proved once. -/
def glueWith (p : SurvivingFlag W i j → SurvivingFlag W i j)
    (hinvol : ∀ f, p (p f) = f) (hne : ∀ f, p f ≠ f) (c : ℕ) :
    Fragment (SurvivingLabel α i j) where
  Flag := SurvivingFlag W i j
  Vertex := W.Vertex
  attach := glueAttach W i j
  pairing := p
  pairing_invol := hinvol
  pairing_ne := hne
  boundaryFlag := glueBoundaryFlag W i j
  attach_boundaryFlag := glue_attach_boundaryFlag W i j
  eq_boundaryFlag := glue_eq_boundaryFlag W i j
  circles := c

/-- Gluing the boundary labels `i ≠ j` when their flags bound a
common edge: the edge closes into a free circle. -/
def gluePairClosed (hclosed : W.pairing (W.boundaryFlag i) = W.boundaryFlag j) :
    Fragment (SurvivingLabel α i j) :=
  glueWith W i j
    (fun f =>
      ⟨W.pairing f.val,
        fun h => f.prop.2 (by
          rw [← W.pairing_invol f.val, h, hclosed]),
        fun h => f.prop.1 (by
          rw [← W.pairing_invol f.val, h, ← hclosed, W.pairing_invol])⟩)
    (fun f => Subtype.ext (W.pairing_invol f.val))
    (fun f h => W.pairing_ne f.val (congrArg Subtype.val h))
    (W.circles + 1)

/-- Gluing the boundary labels `i ≠ j` when their flags bound
distinct edges: the two edges are unified by rewiring. -/
def gluePairOpen (hij : i ≠ j)
    (hopen : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag j) :
    Fragment (SurvivingLabel α i j) :=
  glueWith W i j (rewire hopen) (rewire_invol hij hopen)
    (rewire_ne hij hopen) W.circles

/-- Gluing a pair of distinct boundary labels: the two half-edges at
`i` and `j` are joined.  If they bound a common edge it closes into a
free circle; otherwise their edges are unified end to end. -/
def gluePair (hij : i ≠ j) : Fragment (SurvivingLabel α i j) :=
  if hclosed : W.pairing (W.boundaryFlag i) = W.boundaryFlag j then
    gluePairClosed W i j hclosed
  else
    gluePairOpen W i j hij hclosed

end Glue

/-! ## 3. Isomorphism of fragments

The hypothesis class
asks parameters to be isomorphism-invariant; this is the notion of
isomorphism.  (`RS/Novel/Skein/FragmentEquiv.lean` proves the
equivalences form a groupoid and are congruences for the fragment
operations.) -/

/-- An equivalence of fragments: a pair of type equivalences on
flags and vertices commuting with attachment, pairing, and
boundary-flag data, preserving the circle count. -/
structure Equiv (W₁ W₂ : Fragment α) where
  /-- The equivalence of flag types. -/
  flagEquiv : W₁.Flag ≃ W₂.Flag
  /-- The equivalence of vertex types. -/
  vertexEquiv : W₁.Vertex ≃ W₂.Vertex
  /-- The flag equivalence commutes with attachment. -/
  attach_comm : ∀ f, W₂.attach (flagEquiv f) =
    (W₁.attach f).map vertexEquiv id
  /-- The flag equivalence commutes with pairing. -/
  pairing_comm : ∀ f, flagEquiv (W₁.pairing f) =
    W₂.pairing (flagEquiv f)
  /-- The circle counts agree. -/
  circles_eq : W₁.circles = W₂.circles

end Fragment

/-! ## 4. Composition of fragments

An `(s + t)`-fragment
and a `(t + u)`-fragment compose by gluing the last `t` labels of
the first to the first `t` of the second, top pair first, through
the single-pair gluing above; the label bookkeeping is by one-point
removals of `Fin` indices.  Composition is what the connection
pairing evaluates. -/

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

/-! ## 5. Connection pairings and the edge-rank hypothesis

The connection
pairing of a parameter at arity `t` closes two `t`-fragments
against each other; the edge-rank hypothesis bounds, for every
`t`, the rank of that pairing by `R ^ t`, phrased as the
`Module.rank` of the range of the curried pairing
(`RS/Novel/Skein/ConnectionRank.lean` proves this equivalent to
the finite-submatrix reading of the literature; that equivalence
is a theorem *about* the hypothesis and is not needed to state
it).  `EdgeRankParameter` packages the hypothesis
class of the forward direction: normalized at the empty graph,
isomorphism-invariant, rank-bounded. -/

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

/-! ## 6. Eulerian edge subsets and circuit data

Definition 5 sums over
pairing-closed flag subsets in which every vertex has even degree.
A *transition system* is the local pairing `κ` of Definition 5: a
second fixed-point-free involution matching participating flags at
common vertices.  Following an edge and then the matching generates
the circuit walks; each geometric circuit of `n` edges appears as
two walk-cycles (its two directions) when `n ≥ 2` and as two walk
fixed points when `n = 1`, so the circuit count is half the number
of orbits. -/

variable {α : Type}

/-- An edge subset of a fragment: a flag set closed under the edge
pairing. -/
structure EdgeSubset (W : Fragment α) where
  /-- The participating flags. -/
  flags : Finset W.Flag
  /-- The set is closed under the edge pairing. -/
  pairing_mem : ∀ f ∈ flags, W.pairing f ∈ flags

namespace EdgeSubset

variable {W : Fragment α}

/-- The degree of a vertex within an edge subset: the number of
participating flags attached to it. -/
noncomputable def deg (F : EdgeSubset W) (v : W.Vertex) : ℕ :=
  letI := Classical.decEq (W.Vertex ⊕ α)
  (F.flags.filter (fun f => W.attach f = Sum.inl v)).card

/-- An edge subset is Eulerian when every vertex has even degree
within it. -/
def Eulerian (F : EdgeSubset W) : Prop :=
  ∀ v : W.Vertex, Even (F.deg v)

/-- A transition system on an edge subset: a fixed-point-free
involution of its flags matching flags at a common internal
vertex.  This is the local pairing data `κ` of Definition 5. -/
structure TransitionSystem (F : EdgeSubset W) where
  /-- The matching. -/
  match_ : W.Flag → W.Flag
  /-- The matching is an involution on the participating flags. -/
  match_invol : ∀ f ∈ F.flags, match_ (match_ f) = f
  /-- The matching has no fixed points on the participating flags. -/
  match_ne : ∀ f ∈ F.flags, match_ f ≠ f
  /-- The matching stays within the participating flags. -/
  match_mem : ∀ f ∈ F.flags, match_ f ∈ F.flags
  /-- Matched flags share an internal vertex. -/
  match_vertex : ∀ f ∈ F.flags, ∀ v : W.Vertex,
    W.attach f = Sum.inl v → W.attach (match_ f) = Sum.inl v
  /-- Only internally attached flags participate. -/
  attach_internal : ∀ f ∈ F.flags, ∃ v : W.Vertex,
    W.attach f = Sum.inl v

/-- The walk map of a transition system: follow the edge to the
partner flag, then the matching at its vertex. -/
def TransitionSystem.walk {F : EdgeSubset W} (κ : TransitionSystem F)
    (f : W.Flag) : W.Flag :=
  κ.match_ (W.pairing f)

/-- The walk map preserves the participating flags. -/
theorem TransitionSystem.walk_mem {F : EdgeSubset W}
    (κ : TransitionSystem F) {f : W.Flag} (hf : f ∈ F.flags) :
    κ.walk f ∈ F.flags :=
  κ.match_mem _ (F.pairing_mem f hf)

/-- The walk map is injective on the participating flags. -/
theorem TransitionSystem.walk_injOn {F : EdgeSubset W}
    (κ : TransitionSystem F) {f g : W.Flag} (hf : f ∈ F.flags)
    (hg : g ∈ F.flags) (h : κ.walk f = κ.walk g) : f = g := by
  have hpf : W.pairing f ∈ F.flags := F.pairing_mem f hf
  have hpg : W.pairing g ∈ F.flags := F.pairing_mem g hg
  have hm : W.pairing f = W.pairing g := by
    have h1 := κ.match_invol _ hpf
    have h2 := κ.match_invol _ hpg
    have h' : κ.match_ (W.pairing f) = κ.match_ (W.pairing g) := h
    calc W.pairing f = κ.match_ (κ.match_ (W.pairing f)) := h1.symm
      _ = κ.match_ (κ.match_ (W.pairing g)) := by rw [h']
      _ = W.pairing g := h2
  calc f = W.pairing (W.pairing f) := (W.pairing_invol f).symm
    _ = W.pairing (W.pairing g) := by rw [hm]
    _ = g := W.pairing_invol g

/-- The walk permutation of a transition system: the walk map as a
permutation of the participating flags. -/
noncomputable def TransitionSystem.walkPerm {F : EdgeSubset W}
    (κ : TransitionSystem F) : Equiv.Perm {f : W.Flag // f ∈ F.flags} :=
  Equiv.ofBijective
    (fun f => ⟨κ.walk f.val, κ.walk_mem f.prop⟩)
    (Finite.injective_iff_bijective.mp
      (fun f g h => Subtype.ext
        (κ.walk_injOn f.prop g.prop (congrArg Subtype.val h))))

/-- The circuit count of a transition system: each geometric circuit
of `n` edges carries two walk-cycles of length `n` when `n ≥ 2` and
two walk fixed points when `n = 1`, so the count is half the total
number of orbits. -/
noncomputable def TransitionSystem.circuitCount {F : EdgeSubset W}
    (κ : TransitionSystem F) : ℕ :=
  (κ.walkPerm.cycleType.card +
    Fintype.card (Function.fixedPoints κ.walkPerm)) / 2

end EdgeSubset

/-! ## 7. The mixed partition function (Definition 5)

A `(k, 2ℓ)` mixed
vertex functional assigns a value to a multiset of even colours and
a *set* of odd colours; the alternating evaluation on an ordered
odd list is recovered through the sorting sign, so antisymmetry is
a theorem of the evaluator rather than a condition on the data.
The summand of an Eulerian subset is its circuit sign times the
colouring sum of vertex values, odd colours contributing through
the symplectic pairing (`oddPartner`, `oddPartnerSign`); the value
of the subset is choice-free because the tree proves it independent
of the transition data, and `mixedPartition` is the free-circle
factor `(k − 2ℓ)^circles` times the sum over Eulerian subsets. -/

/-- The data of a `(k, 2ℓ)` mixed vertex functional: a value for
each multiset of even colours and set of odd colours. -/
def MixedFunctional (k ℓ : ℕ) : Type :=
  Multiset (Fin k) → Finset (Fin (2 * ℓ)) → ℂ

/-- The alternating evaluation of a mixed functional on an ordered
list of odd colours: zero on repetitions, otherwise the sorting
sign times the value on the underlying set. -/
def MixedFunctional.evalOdd {k ℓ : ℕ} (h : MixedFunctional k ℓ)
    (μ : Multiset (Fin k)) (w : List (Fin (2 * ℓ))) : ℂ :=
  if w.Nodup then (sortSign w : ℂ) * h μ w.toFinset else 0

/-- The odd-colour index pairing of the standard symplectic basis:
the partner of colour `c` is `c + ℓ` when `c < ℓ` and `c − ℓ`
otherwise. -/
def oddPartner (ℓ : ℕ) (c : Fin (2 * ℓ)) : Fin (2 * ℓ) :=
  if h : c.val < ℓ then ⟨c.val + ℓ, by omega⟩
  else ⟨c.val - ℓ, by omega⟩

/-- The sign of the odd-colour pairing: `g_c = −f_{c+ℓ}` for
`c < ℓ` and `g_c = f_{c−ℓ}` otherwise. -/
def oddPartnerSign (ℓ : ℕ) (c : Fin (2 * ℓ)) : ℤ :=
  if c.val < ℓ then -1 else 1

/-- An orientation compatible with a transition system: an in/out
designation of the participating flags, flipped both by the vertex
matching and by the edge pairing (so circuits are traversed
consistently). -/
structure EdgeSubset.TransitionSystem.Orientation {α : Type}
    {W : Fragment α} {F : EdgeSubset W}
    (κ : F.TransitionSystem) where
  /-- Whether a flag is an outgoing end. -/
  isOut : W.Flag → Bool
  /-- The vertex matching pairs incoming with outgoing flags. -/
  match_flip : ∀ f ∈ F.flags, isOut (κ.match_ f) = !isOut f
  /-- Each edge has one outgoing and one incoming end. -/
  pairing_flip : ∀ f ∈ F.flags, isOut (W.pairing f) = !isOut f

-- Deliberately semireducible: the order is an enumeration artefact,
-- only ever supplied explicitly via `letI`, never by instance search.
set_option warn.classDefReducibility false in
/-- An arbitrary but fixed linear order on the flags of a fragment,
transported from an enumeration.  Used only to enumerate vertex
pairings; the evaluated summands are independent of the choice
because pair blocks move by even permutations. -/
noncomputable def Fragment.flagOrder {α : Type} (W : Fragment α) :
    LinearOrder W.Flag :=
  LinearOrder.lift' (Fintype.equivFin W.Flag)
    (Fintype.equivFin W.Flag).injective

/-- The incoming participating flags at a vertex, in the fixed flag
order. -/
noncomputable def EdgeSubset.inFlagsAt {α : Type} {W : Fragment α}
    (F : EdgeSubset W) {κ : F.TransitionSystem}
    (o : κ.Orientation) (v : W.Vertex) : List W.Flag :=
  letI := W.flagOrder
  letI := Classical.dec
  (F.flags.filter
      (fun f => W.attach f = Sum.inl v ∧ o.isOut f = false)).sort (· ≤ ·)

section Summand

variable {α : Type} {W : Fragment α}

/-- The complement of an edge subset is closed under the pairing. -/
theorem EdgeSubset.pairing_not_mem (F : EdgeSubset W) {f : W.Flag}
    (hf : f ∉ F.flags) : W.pairing f ∉ F.flags := fun hmem => by
  have := F.pairing_mem _ hmem
  rw [W.pairing_invol] at this
  exact hf this

/-- Even colourings of the non-participating edges: pairing-constant
colours on the flags outside the subset. -/
def EdgeSubset.EvenColouring (F : EdgeSubset W) (k : ℕ) : Type :=
  {ψ : {f : W.Flag // f ∉ F.flags} → Fin k //
    ∀ f : {f : W.Flag // f ∉ F.flags},
      ψ ⟨W.pairing f.val, F.pairing_not_mem f.prop⟩ = ψ f}

/-- Odd colourings of the participating edges: pairing-constant
colours on the flags of the subset. -/
def EdgeSubset.OddColouring (F : EdgeSubset W) (ℓ : ℕ) : Type :=
  {φ : {f : W.Flag // f ∈ F.flags} → Fin (2 * ℓ) //
    ∀ f : {f : W.Flag // f ∈ F.flags},
      φ ⟨W.pairing f.val, F.pairing_mem _ f.prop⟩ = φ f}

open Classical in
/-- Even colourings are finite in number. -/
noncomputable instance EdgeSubset.EvenColouring.instFintype
    (F : EdgeSubset W) (k : ℕ) : Fintype (F.EvenColouring k) := by
  unfold EdgeSubset.EvenColouring
  infer_instance

open Classical in
/-- And so are odd ones, so Definition 5's sum is finite. -/
noncomputable instance EdgeSubset.OddColouring.instFintype
    (F : EdgeSubset W) (ℓ : ℕ) : Fintype (F.OddColouring ℓ) := by
  unfold EdgeSubset.OddColouring
  infer_instance

open Classical in
/-- The even-colour multiset at a vertex: the colours of the
non-participating flags attached to it. -/
noncomputable def EdgeSubset.evenColoursAt (F : EdgeSubset W) {k : ℕ}
    (ψ : F.EvenColouring k) (v : W.Vertex) : Multiset (Fin k) :=
  ((Finset.univ.filter
      (fun f : {f : W.Flag // f ∉ F.flags} =>
        W.attach f.val = Sum.inl v)).val).map ψ.val

/-- Every in-flag at a vertex participates in the edge subset. -/
theorem EdgeSubset.mem_of_mem_inFlagsAt {F : EdgeSubset W}
    {κ : F.TransitionSystem} {o : κ.Orientation} {v : W.Vertex}
    {f : W.Flag} (hf : f ∈ F.inFlagsAt o v) : f ∈ F.flags := by
  letI := W.flagOrder
  letI := Classical.dec
  unfold EdgeSubset.inFlagsAt at hf
  exact (Finset.mem_filter.mp ((Finset.mem_sort _).mp hf)).1

open Classical in
/-- The odd pair contributed by an incoming participating flag: its
edge colour followed by the partner index of its matched outgoing
flag's edge colour. -/
noncomputable def EdgeSubset.oddPairFn (F : EdgeSubset W) {ℓ : ℕ}
    (κ : F.TransitionSystem) (φ : F.OddColouring ℓ)
    (f : {f : W.Flag // f ∈ F.flags}) : List (Fin (2 * ℓ)) :=
  [φ.val f, oddPartner ℓ (φ.val ⟨κ.match_ f.val, κ.match_mem _ f.prop⟩)]

open Classical in
/-- The odd-pairing sign contributed by an incoming participating
flag: the partner sign of its matched outgoing flag's colour. -/
noncomputable def EdgeSubset.oddSignFn (F : EdgeSubset W) {ℓ : ℕ}
    (κ : F.TransitionSystem) (φ : F.OddColouring ℓ)
    (f : {f : W.Flag // f ∈ F.flags}) : ℤ :=
  oddPartnerSign ℓ (φ.val ⟨κ.match_ f.val, κ.match_mem _ f.prop⟩)

open Classical in
/-- The odd-colour list at a vertex: the odd pairs of the incoming
flags in the fixed order. -/
noncomputable def EdgeSubset.oddListAt (F : EdgeSubset W) {ℓ : ℕ}
    {κ : F.TransitionSystem} (o : κ.Orientation)
    (φ : F.OddColouring ℓ) (v : W.Vertex) : List (Fin (2 * ℓ)) :=
  ((F.inFlagsAt o v).attachWith (· ∈ F.flags)
      (fun _ hf => F.mem_of_mem_inFlagsAt hf)).flatMap (F.oddPairFn κ φ)

open Classical in
/-- The odd-pairing sign at a vertex: the product of the partner
signs of the outgoing colours. -/
noncomputable def EdgeSubset.oddSignAt (F : EdgeSubset W) {ℓ : ℕ}
    {κ : F.TransitionSystem} (o : κ.Orientation)
    (φ : F.OddColouring ℓ) (v : W.Vertex) : ℤ :=
  (((F.inFlagsAt o v).attachWith (· ∈ F.flags)
      (fun _ hf => F.mem_of_mem_inFlagsAt hf)).map (F.oddSignFn κ φ)).prod

open Classical in
/-- The Definition 5 summand of an Eulerian edge subset with chosen
transition system and orientation: the circuit sign times the
colouring sum of the vertex values. -/
noncomputable def EdgeSubset.mixedSummand (F : EdgeSubset W)
    {k ℓ : ℕ} (h : MixedFunctional k ℓ)
    {κ : F.TransitionSystem} (o : κ.Orientation) : ℂ :=
  ((-1 : ℂ) ^ κ.circuitCount) *
    ∑ ψ : F.EvenColouring k, ∑ φ : F.OddColouring ℓ,
      ∏ v : W.Vertex,
        ((F.oddSignAt o φ v : ℂ) *
          h.evalOdd (F.evenColoursAt ψ v) (F.oddListAt o φ v))

open Classical in
/-- The Definition 5 value of an edge subset: the summand for a
choice of transition system and orientation, zero when none
exists.  (Every Eulerian subset admits one; the value is
independent of the choice by the Eulerian-independence input.) -/
noncomputable def EdgeSubset.mixedValue (F : EdgeSubset W)
    {k ℓ : ℕ} (h : MixedFunctional k ℓ) : ℂ :=
  if hne : Nonempty ((κ : F.TransitionSystem) × κ.Orientation) then
    F.mixedSummand h (Classical.choice hne).2
  else 0

end Summand

open Classical in
/-- **The mixed partition function** (Regts–Sevenster Definition 5)
of a fragment: the free-circle factor times the sum over Eulerian
edge subsets of their circuit-signed colouring sums. -/
noncomputable def mixedPartition {α : Type} {k ℓ : ℕ}
    (h : MixedFunctional k ℓ) (W : Fragment α) : ℂ :=
  ((k : ℂ) - 2 * ℓ) ^ W.circles *
    ∑ s : Finset W.Flag,
      if hc : ∀ f ∈ s, W.pairing f ∈ s then
        if (EdgeSubset.mk s hc).Eulerian then
          (EdgeSubset.mk s hc).mixedValue h
        else 0
      else 0

/-- A parameter on closed fragments is a mixed partition function
when it is the Definition 5 value of some mixed functional. -/
def IsMixedPartitionFunction (f : ClosedFragment → ℂ) : Prop :=
  ∃ (k ℓ : ℕ) (h : MixedFunctional k ℓ),
    ∀ W : ClosedFragment, f W = mixedPartition h W

/-! ## 8. The named statements

The forward direction, its quantitative form with the paper's
dimension bound `⌊2eR⌋`, and the converse with its explicit
base. -/

/-- **THE REGTS–SEVENSTER CONJECTURE.**  Every graph parameter with
exponentially bounded edge-connection rank is a mixed partition
function. -/
def RegtsSevensterStatement : Prop :=
  ∀ (R : ℕ) (f : EdgeRankParameter R), IsMixedPartitionFunction f.val

/-- A mixed partition function with explicit dimension bounds: the
functional's even dimension `k` and odd dimension `2ℓ` are both at
most `B`. -/
def IsMixedPartitionFunctionBounded (f : ClosedFragment → ℂ)
    (B : ℕ) : Prop :=
  ∃ (k ℓ : ℕ) (h : MixedFunctional k ℓ),
    k ≤ B ∧ 2 * ℓ ≤ B ∧
      ∀ W : ClosedFragment, f W = mixedPartition h W

/-- **THE QUANTITATIVE REGTS–SEVENSTER STATEMENT**: every graph
parameter with edge-connection rank at most `R ^ t` is a mixed
partition function of a `(k, 2ℓ)`-functional with
`k, 2ℓ ≤ ⌊2eR⌋`. -/
def RegtsSevensterStatementQuant : Prop :=
  ∀ (R : ℕ) (f : EdgeRankParameter R),
    IsMixedPartitionFunctionBounded f.val
      ⌊2 * Real.exp 1 * (R : ℝ)⌋₊

/-- **THE CONVERSE STATEMENT**: every mixed partition function is
an edge-rank-bounded parameter with base `max 1 (k + 2ℓ)`
(Regts–Sevenster, arXiv:1807.04494, Theorem 6). -/
def RegtsSevensterConverseStatement : Prop :=
  ∀ (k ℓ : ℕ) (h : MixedFunctional k ℓ),
    ∃ g : EdgeRankParameter (max 1 (k + 2 * ℓ)),
      ∀ W : ClosedFragment, g.val W = mixedPartition h W


end RS

/-! ## 9. The theorems of record

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
