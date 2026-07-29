import RS.Common.MathlibDeps

/-!
# Flag-graph model of multigraph fragments

A *fragment* over a label type `α` is a finite multigraph in
half-edge (flag) form: finite types of flags and internal vertices,
an attachment map sending each flag either to an internal vertex or
to a boundary label, a fixed-point-free involution on flags (whose
orbits are edges), a distinguished flag at each boundary label with
each label hit exactly once, and a separate count of free circles.
A flag attached to a boundary label models a pendant half-edge; no
vertex sits at a boundary end.

Gluing is built from the single-pair primitive `gluePair`, which
glues the two half-edges at a chosen pair of distinct labels: if
they bound a common edge, that edge closes into a free circle;
otherwise the two edges are unified by rewiring their far ends.
Multi-label gluing is iterated single-pair gluing; the boundary
labels of intermediate stages are subtypes of `α`, and `relabel`
transports along label equivalences.
-/

namespace RS

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

/-! ### The strand -/

/-- The strand: a single edge with two boundary flags and no internal
vertices.  The identity 2-fragment. -/
def strand : Fragment (Fin 2) where
  Flag := Fin 2
  Vertex := Empty
  attach := fun f => Sum.inr f
  pairing := fun f => ⟨1 - f.val, by omega⟩
  pairing_invol := fun f => by ext; simp; omega
  pairing_ne := fun f => by
    intro h
    have := congr_arg Fin.val h
    simp at this
    omega
  boundaryFlag := id
  attach_boundaryFlag := fun ℓ => rfl
  eq_boundaryFlag := fun ℓ f h => Sum.inr.inj h
  circles := 0

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

/-! ### Relabelling and disjoint union -/

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

private theorem glueAttach_inr {f : SurvivingFlag W i j}
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

private theorem glue_attach_boundaryFlag (ℓ : SurvivingLabel α i j) :
    glueAttach W i j (glueBoundaryFlag W i j ℓ) = Sum.inr ℓ :=
  glueAttach_inr.mpr (W.attach_boundaryFlag ℓ.val)

private theorem glue_eq_boundaryFlag (ℓ : SurvivingLabel α i j)
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

/-- The closed branch of `gluePair`. -/
theorem gluePair_eq_closed {W : Fragment α} {i j : α} (hij : i ≠ j)
    (hclosed : W.pairing (W.boundaryFlag i) = W.boundaryFlag j) :
    W.gluePair i j hij = W.gluePairClosed i j hclosed :=
  dif_pos hclosed

/-- The open branch of `gluePair`. -/
theorem gluePair_eq_open {W : Fragment α} {i j : α} (hij : i ≠ j)
    (hopen : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag j) :
    W.gluePair i j hij = W.gluePairOpen i j hij hopen :=
  dif_neg hopen

end Glue

/-! ### Sanity checks -/

/-- Closing the strand onto itself yields one free circle. -/
example :
    (strand.gluePair 0 1 (by decide)).circles = 1 := by
  rw [gluePair, dif_pos (by decide)]
  rfl

/-- Closing the strand onto itself leaves no flags. -/
example : (strand.gluePair 0 1 (by decide)).Flag → False := by
  decide

end Fragment

end RS
