import RS.Common.ListSign
import RS.Novel.Skein.Eulerian

/-!
# Mixed partition functions: the vertex functional

The data of a mixed partition function (Regts–Sevenster
arXiv:1807.04494, Definition 5) in elementary coordinates: a
`(k, 2ℓ)`-functional assigns a complex value to a multiset of even
colours together with a *set* of odd colours; the alternating
evaluation on an ordered list of odd colours is recovered by the
inversion sign, vanishing on repetitions.

Representing the odd part by its value on sets makes the
antisymmetry a theorem of the evaluator rather than a condition on
the data: reordering an odd list changes `evalOdd` by the sign of
the permutation, and lists with repeated colours evaluate to zero.
-/

namespace RS

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

/-- Evaluation on a list with a repetition vanishes. -/
theorem MixedFunctional.evalOdd_of_not_nodup {k ℓ : ℕ}
    (h : MixedFunctional k ℓ) (μ : Multiset (Fin k))
    {w : List (Fin (2 * ℓ))} (hw : ¬ w.Nodup) :
    h.evalOdd μ w = 0 := by
  simp [MixedFunctional.evalOdd, hw]

/-- Swapping distinct adjacent odd colours flips the alternating
evaluation. -/
theorem MixedFunctional.evalOdd_swap_adjacent {k ℓ : ℕ}
    (h : MixedFunctional k ℓ) (μ : Multiset (Fin k))
    (l₁ l₂ : List (Fin (2 * ℓ))) {a b : Fin (2 * ℓ)} (hab : a ≠ b) :
    h.evalOdd μ (l₁ ++ b :: a :: l₂) =
      -h.evalOdd μ (l₁ ++ a :: b :: l₂) := by
  unfold MixedFunctional.evalOdd
  have hperm : (l₁ ++ b :: a :: l₂).Perm (l₁ ++ a :: b :: l₂) :=
    List.Perm.append_left l₁ (List.Perm.swap a b l₂)
  by_cases hnd : (l₁ ++ a :: b :: l₂).Nodup
  · have hnd' : (l₁ ++ b :: a :: l₂).Nodup := hperm.nodup_iff.mpr hnd
    rw [if_pos hnd', if_pos hnd, sortSign_swap_adjacent l₁ l₂ hab,
      show (l₁ ++ b :: a :: l₂).toFinset =
          (l₁ ++ a :: b :: l₂).toFinset from
        Finset.ext fun x => by
          simp only [List.mem_toFinset]
          exact hperm.mem_iff]
    push_cast
    ring
  · rw [if_neg (fun hh => hnd (hperm.nodup_iff.mp hh)), if_neg hnd,
      neg_zero]

/-- Moving a two-element block of odd colours past another preserves
the alternating evaluation. -/
theorem MixedFunctional.evalOdd_pair_block_swap {k ℓ : ℕ}
    (h : MixedFunctional k ℓ) (μ : Multiset (Fin k))
    (l₁ l₂ : List (Fin (2 * ℓ))) {p₁ p₂ q₁ q₂ : Fin (2 * ℓ)}
    (hp₁q₁ : p₁ ≠ q₁) (hp₁q₂ : p₁ ≠ q₂)
    (hp₂q₁ : p₂ ≠ q₁) (hp₂q₂ : p₂ ≠ q₂) :
    h.evalOdd μ (l₁ ++ q₁ :: q₂ :: p₁ :: p₂ :: l₂) =
      h.evalOdd μ (l₁ ++ p₁ :: p₂ :: q₁ :: q₂ :: l₂) := by
  unfold MixedFunctional.evalOdd
  have hperm : (l₁ ++ q₁ :: q₂ :: p₁ :: p₂ :: l₂).Perm
      (l₁ ++ p₁ :: p₂ :: q₁ :: q₂ :: l₂) := by
    refine List.Perm.append_left l₁ ?_
    have hblocks : ([q₁, q₂] ++ [p₁, p₂]).Perm ([p₁, p₂] ++ [q₁, q₂]) :=
      List.perm_append_comm
    simpa using hblocks.append_right l₂
  by_cases hnd : (l₁ ++ p₁ :: p₂ :: q₁ :: q₂ :: l₂).Nodup
  · have hnd' := hperm.nodup_iff.mpr hnd
    rw [if_pos hnd', if_pos hnd,
      sortSign_pair_block_swap l₁ l₂ hp₁q₁ hp₁q₂ hp₂q₁ hp₂q₂,
      show (l₁ ++ q₁ :: q₂ :: p₁ :: p₂ :: l₂).toFinset =
          (l₁ ++ p₁ :: p₂ :: q₁ :: q₂ :: l₂).toFinset from
        Finset.ext fun x => by
          simp only [List.mem_toFinset]
          exact hperm.mem_iff]
  · rw [if_neg (fun hh => hnd (hperm.nodup_iff.mp hh)), if_neg hnd]

/-- The alternating evaluation is invariant under permuting a list
of length-two blocks: each transposition of adjacent blocks moves
an even number of elements. -/
theorem MixedFunctional.evalOdd_flatMap_perm {k ℓ : ℕ}
    (h : MixedFunctional k ℓ) (μ : Multiset (Fin k)) {β : Type}
    (pairFn : β → List (Fin (2 * ℓ)))
    (hlen : ∀ b, (pairFn b).length = 2)
    {l₁ l₂ : List β} (hperm : l₁.Perm l₂) :
    ∀ pre : List (Fin (2 * ℓ)),
      h.evalOdd μ (pre ++ l₁.flatMap pairFn) =
        h.evalOdd μ (pre ++ l₂.flatMap pairFn) := by
  induction hperm with
  | nil => intro pre; rfl
  | cons b _ ih =>
    intro pre
    simp only [List.flatMap_cons, ← List.append_assoc]
    exact ih (pre ++ pairFn b)
  | swap p q rest =>
    intro pre
    obtain ⟨q₁, q₂, hq⟩ := List.length_eq_two.mp (hlen q)
    obtain ⟨p₁, p₂, hp⟩ := List.length_eq_two.mp (hlen p)
    simp only [List.flatMap_cons, hp, hq, List.cons_append,
      List.nil_append]
    by_cases hnd :
        (pre ++ p₁ :: p₂ :: q₁ :: q₂ :: rest.flatMap pairFn).Nodup
    · have hnd4 := hnd
      rw [List.nodup_append] at hnd4
      have hfour := hnd4.2.1
      simp only [List.nodup_cons, List.mem_cons] at hfour
      exact h.evalOdd_pair_block_swap μ pre (rest.flatMap pairFn)
        (fun he => hfour.1 (Or.inr (Or.inl he)))
        (fun he => hfour.1 (Or.inr (Or.inr (Or.inl he))))
        (fun he => hfour.2.1 (Or.inl he))
        (fun he => hfour.2.1 (Or.inr (Or.inl he)))
    · have hperm2 :
          (pre ++ q₁ :: q₂ :: p₁ :: p₂ :: rest.flatMap pairFn).Perm
            (pre ++ p₁ :: p₂ :: q₁ :: q₂ :: rest.flatMap pairFn) := by
        refine List.Perm.append_left pre ?_
        have hblocks : ([q₁, q₂] ++ [p₁, p₂]).Perm
            ([p₁, p₂] ++ [q₁, q₂]) := List.perm_append_comm
        simpa using hblocks.append_right (rest.flatMap pairFn)
      rw [h.evalOdd_of_not_nodup μ
          (fun hh => hnd (hperm2.nodup_iff.mp hh)),
        h.evalOdd_of_not_nodup μ hnd]
  | trans _ _ ih₁ ih₂ =>
    intro pre
    exact (ih₁ pre).trans (ih₂ pre)

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

/-- The odd-colour pairing is an involution. -/
theorem oddPartner_invol (ℓ : ℕ) (c : Fin (2 * ℓ)) :
    oddPartner ℓ (oddPartner ℓ c) = c := by
  unfold oddPartner
  by_cases h : c.val < ℓ
  · rw [dif_pos h, dif_neg (show ¬ c.val + ℓ < ℓ by omega)]
    exact Fin.ext (by show c.val + ℓ - ℓ = c.val; omega)
  · have hc : c.val < 2 * ℓ := c.isLt
    rw [dif_neg h, dif_pos (show c.val - ℓ < ℓ by omega)]
    exact Fin.ext (by show c.val - ℓ + ℓ = c.val; omega)

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

/-- Transport of an orientation along a fragment equivalence. -/
noncomputable def EdgeSubset.TransitionSystem.Orientation.transport
    {W₁ W₂ : Fragment α} (e : W₁.Equiv W₂) {F : EdgeSubset W₁}
    {κ : F.TransitionSystem} (o : κ.Orientation) :
    (κ.transport e).Orientation where
  isOut := fun f => o.isOut (e.flagEquiv.symm f)
  match_flip := fun f hf => by
    show o.isOut (e.flagEquiv.symm
      (e.flagEquiv (κ.match_ (e.flagEquiv.symm f)))) = _
    rw [Equiv.symm_apply_apply]
    exact o.match_flip _ ((EdgeSubset.mem_transport_iff e F f).mp hf)
  pairing_flip := fun f hf => by
    show o.isOut (e.flagEquiv.symm (W₂.pairing f)) = _
    have hp := e.pairing_comm (e.flagEquiv.symm f)
    rw [Equiv.apply_symm_apply] at hp
    rw [← hp, Equiv.symm_apply_apply]
    exact o.pairing_flip _ ((EdgeSubset.mem_transport_iff e F f).mp hf)

/-- The complement flag equivalence of a transported edge
subset. -/
noncomputable def EdgeSubset.transportComplEquiv {W₁ W₂ : Fragment α}
    (e : W₁.Equiv W₂) (F : EdgeSubset W₁) :
    {f : W₁.Flag // f ∉ F.flags} ≃
      {f : W₂.Flag // f ∉ (EdgeSubset.transport e F).flags} :=
  e.flagEquiv.subtypeEquiv (fun f => by
    rw [EdgeSubset.mem_transport_iff, Equiv.symm_apply_apply])

/-- Transport of even colourings along a fragment equivalence. -/
noncomputable def EdgeSubset.EvenColouring.transport
    {W₁ W₂ : Fragment α} (e : W₁.Equiv W₂) {F : EdgeSubset W₁}
    {k : ℕ} (ψ : F.EvenColouring k) :
    (EdgeSubset.transport e F).EvenColouring k :=
  ⟨fun f => ψ.val ((EdgeSubset.transportComplEquiv e F).symm f),
   fun f => by
    have harg : e.flagEquiv.symm (W₂.pairing f.val) =
        W₁.pairing (e.flagEquiv.symm f.val) := by
      have hp := e.pairing_comm (e.flagEquiv.symm f.val)
      rw [Equiv.apply_symm_apply] at hp
      rw [← hp, Equiv.symm_apply_apply]
    exact (congrArg ψ.val (Subtype.ext harg)).trans (ψ.prop _)⟩

/-- Transport of odd colourings along a fragment equivalence. -/
noncomputable def EdgeSubset.OddColouring.transport
    {W₁ W₂ : Fragment α} (e : W₁.Equiv W₂) {F : EdgeSubset W₁}
    {ℓ : ℕ} (φ : F.OddColouring ℓ) :
    (EdgeSubset.transport e F).OddColouring ℓ :=
  ⟨fun f => φ.val ((EdgeSubset.transportFlagsEquiv e F).symm f),
   fun f => by
    have harg : e.flagEquiv.symm (W₂.pairing f.val) =
        W₁.pairing (e.flagEquiv.symm f.val) := by
      have hp := e.pairing_comm (e.flagEquiv.symm f.val)
      rw [Equiv.apply_symm_apply] at hp
      rw [← hp, Equiv.symm_apply_apply]
    exact (congrArg φ.val (Subtype.ext harg)).trans (φ.prop _)⟩

open Classical in
/-- The even-colour multiset is preserved by transport. -/
theorem EdgeSubset.evenColoursAt_transport {W₁ W₂ : Fragment α}
    (e : W₁.Equiv W₂) {F : EdgeSubset W₁} {k : ℕ}
    (ψ : F.EvenColouring k) (v : W₁.Vertex) :
    (EdgeSubset.transport e F).evenColoursAt
        (EdgeSubset.EvenColouring.transport e ψ) (e.vertexEquiv v) =
      F.evenColoursAt ψ v := by
  unfold EdgeSubset.evenColoursAt
  rw [show (Finset.univ :
      Finset {f : W₂.Flag // f ∉ (EdgeSubset.transport e F).flags}) =
      Finset.univ.map (EdgeSubset.transportComplEquiv e F).toEmbedding
    from (Finset.map_univ_equiv _).symm]
  rw [Finset.filter_map]
  rw [show ((Finset.filter _ Finset.univ).map
      (EdgeSubset.transportComplEquiv e F).toEmbedding).val =
      (Finset.filter _ Finset.univ).val.map
        (EdgeSubset.transportComplEquiv e F) from rfl]
  rw [Multiset.map_map]
  congr 1
  · funext x
    show ψ.val ((EdgeSubset.transportComplEquiv e F).symm
      ((EdgeSubset.transportComplEquiv e F) x)) = ψ.val x
    rw [Equiv.symm_apply_apply]
  · have hfilter : Finset.filter
        ((fun f => W₂.attach f.val = Sum.inl (e.vertexEquiv v)) ∘
          (EdgeSubset.transportComplEquiv e F).toEmbedding)
        Finset.univ =
        Finset.filter
          (fun f : {f : W₁.Flag // f ∉ F.flags} =>
            W₁.attach f.val = Sum.inl v) Finset.univ := by
      apply Finset.filter_congr
      intro f _
      rw [Function.comp_apply, Equiv.coe_toEmbedding]
      constructor
      · intro hf
        have hcomm := e.attach_comm f.val
        rw [show ((EdgeSubset.transportComplEquiv e F) f).val =
            e.flagEquiv f.val from rfl] at hf
        rw [hf] at hcomm
        rcases ha : W₁.attach f.val with w | ℓ
        · rw [ha] at hcomm
          simp only [Sum.map_inl] at hcomm
          exact congrArg Sum.inl
            (e.vertexEquiv.injective (Sum.inl.inj hcomm.symm))
        · rw [ha] at hcomm
          simp at hcomm
      · intro hf
        have hcomm := e.attach_comm f.val
        rw [hf] at hcomm
        rw [show ((EdgeSubset.transportComplEquiv e F) f).val =
          e.flagEquiv f.val from rfl]
        simpa using hcomm
    rw [hfilter]

open Classical in
/-- The transported in-flag list is a permutation of the image of
the original: both enumerate the same transported filter set. -/
theorem EdgeSubset.inFlagsAt_transport_perm {W₁ W₂ : Fragment α}
    (e : W₁.Equiv W₂) {F : EdgeSubset W₁}
    {κ : F.TransitionSystem} (o : κ.Orientation) (v : W₁.Vertex) :
    ((EdgeSubset.transport e F).inFlagsAt
        (EdgeSubset.TransitionSystem.Orientation.transport e o)
        (e.vertexEquiv v)).Perm
      ((F.inFlagsAt o v).map e.flagEquiv) := by
  rw [← Multiset.coe_eq_coe]
  unfold EdgeSubset.inFlagsAt
  rw [Finset.sort_eq, ← Multiset.map_coe, Finset.sort_eq]
  refine (Multiset.Nodup.ext ?_ ?_).mpr ?_
  · exact Finset.nodup _
  · exact Multiset.Nodup.map e.flagEquiv.injective (Finset.nodup _)
  · intro g
    simp only [Finset.mem_val, Multiset.mem_map, Finset.mem_filter,
      EdgeSubset.mem_transport_iff]
    constructor
    · rintro ⟨hmem, hatt, hout⟩
      refine ⟨e.flagEquiv.symm g, ⟨hmem, ?_, ?_⟩, ?_⟩
      · have hcomm := e.attach_comm (e.flagEquiv.symm g)
        rw [Equiv.apply_symm_apply, hatt] at hcomm
        rcases ha : W₁.attach (e.flagEquiv.symm g) with w | ℓ
        · rw [ha] at hcomm
          simp only [Sum.map_inl] at hcomm
          exact congrArg Sum.inl
            (e.vertexEquiv.injective (Sum.inl.inj hcomm)).symm
        · rw [ha] at hcomm
          simp at hcomm
      · exact hout
      · exact Equiv.apply_symm_apply _ _
    · rintro ⟨x, ⟨hmem, hatt, hout⟩, rfl⟩
      refine ⟨?_, ?_, ?_⟩
      · rwa [Equiv.symm_apply_apply]
      · have hcomm := e.attach_comm x
        rw [hatt] at hcomm
        simpa using hcomm
      · show o.isOut (e.flagEquiv.symm (e.flagEquiv x)) = false
        rwa [Equiv.symm_apply_apply]

/-- A transported odd colouring evaluated at a transported flag is
the original colour. -/
theorem EdgeSubset.OddColouring.transport_apply {W₁ W₂ : Fragment α}
    (e : W₁.Equiv W₂) {F : EdgeSubset W₁} {ℓ : ℕ}
    (φ : F.OddColouring ℓ) (g : W₁.Flag) (hg : g ∈ F.flags)
    (hg' : e.flagEquiv g ∈ (EdgeSubset.transport e F).flags) :
    (EdgeSubset.OddColouring.transport e φ).val ⟨e.flagEquiv g, hg'⟩ =
      φ.val ⟨g, hg⟩ := by
  show φ.val
    ((EdgeSubset.transportFlagsEquiv e F).symm ⟨e.flagEquiv g, hg'⟩) = _
  exact congrArg φ.val (Subtype.ext (Equiv.symm_apply_apply _ _))

/-- The transported matching at a transported flag is the
transported matched flag. -/
theorem EdgeSubset.TransitionSystem.transport_match
    {W₁ W₂ : Fragment α} (e : W₁.Equiv W₂) {F : EdgeSubset W₁}
    (κ : F.TransitionSystem) (g : W₁.Flag) :
    (κ.transport e).match_ (e.flagEquiv g) =
      e.flagEquiv (κ.match_ g) := by
  show e.flagEquiv (κ.match_ (e.flagEquiv.symm (e.flagEquiv g))) = _
  rw [Equiv.symm_apply_apply]

open Classical in
/-- The odd pair at a transported flag under transported data is
the original odd pair. -/
theorem EdgeSubset.oddPairFn_transport {W₁ W₂ : Fragment α}
    (e : W₁.Equiv W₂) {F : EdgeSubset W₁} {ℓ : ℕ}
    (κ : F.TransitionSystem) (φ : F.OddColouring ℓ)
    (f : {f : W₁.Flag // f ∈ F.flags})
    (hf : e.flagEquiv f.val ∈ (EdgeSubset.transport e F).flags) :
    (EdgeSubset.transport e F).oddPairFn (κ.transport e)
        (EdgeSubset.OddColouring.transport e φ)
        ⟨e.flagEquiv f.val, hf⟩ =
      F.oddPairFn κ φ f := by
  unfold EdgeSubset.oddPairFn
  simp only [EdgeSubset.TransitionSystem.transport_match]
  rw [EdgeSubset.OddColouring.transport_apply e φ f.val f.prop,
    EdgeSubset.OddColouring.transport_apply e φ (κ.match_ f.val)
      (κ.match_mem _ f.prop)]

open Classical in
/-- The odd sign at a transported flag under transported data is
the original odd sign. -/
theorem EdgeSubset.oddSignFn_transport {W₁ W₂ : Fragment α}
    (e : W₁.Equiv W₂) {F : EdgeSubset W₁} {ℓ : ℕ}
    (κ : F.TransitionSystem) (φ : F.OddColouring ℓ)
    (f : {f : W₁.Flag // f ∈ F.flags})
    (hf : e.flagEquiv f.val ∈ (EdgeSubset.transport e F).flags) :
    (EdgeSubset.transport e F).oddSignFn (κ.transport e)
        (EdgeSubset.OddColouring.transport e φ)
        ⟨e.flagEquiv f.val, hf⟩ =
      F.oddSignFn κ φ f := by
  unfold EdgeSubset.oddSignFn
  simp only [EdgeSubset.TransitionSystem.transport_match]
  rw [EdgeSubset.OddColouring.transport_apply e φ (κ.match_ f.val)
    (κ.match_mem _ f.prop)]

open Classical in
/-- Membership of the flags of a mapped in-flag list. -/
private theorem mem_transport_of_mem_map_inFlagsAt {W₁ W₂ : Fragment α}
    (e : W₁.Equiv W₂) {F : EdgeSubset W₁} {κ : F.TransitionSystem}
    {o : κ.Orientation} {v : W₁.Vertex} {g : W₂.Flag}
    (hg : g ∈ (F.inFlagsAt o v).map e.flagEquiv) :
    g ∈ (EdgeSubset.transport e F).flags := by
  obtain ⟨f, hfl, rfl⟩ := List.mem_map.mp hg
  rw [EdgeSubset.mem_transport_iff, Equiv.symm_apply_apply]
  exact F.mem_of_mem_inFlagsAt hfl

open Classical in
/-- The odd sign at a vertex is preserved by transport. -/
theorem EdgeSubset.oddSignAt_transport {W₁ W₂ : Fragment α}
    (e : W₁.Equiv W₂) {F : EdgeSubset W₁} {ℓ : ℕ}
    {κ : F.TransitionSystem} (o : κ.Orientation)
    (φ : F.OddColouring ℓ) (v : W₁.Vertex) :
    (EdgeSubset.transport e F).oddSignAt
        (EdgeSubset.TransitionSystem.Orientation.transport e o)
        (EdgeSubset.OddColouring.transport e φ) (e.vertexEquiv v) =
      F.oddSignAt o φ v := by
  unfold EdgeSubset.oddSignAt
  have hstep := perm_pmap Subtype.mk (F.inFlagsAt_transport_perm e o v)
    (fun _ hf => EdgeSubset.mem_of_mem_inFlagsAt hf)
    (fun _ hg => mem_transport_of_mem_map_inFlagsAt e hg)
  refine ((hstep.map ((EdgeSubset.transport e F).oddSignFn
      (κ.transport e) (EdgeSubset.OddColouring.transport e φ))).prod_eq).trans
        ?_
  rw [List.map_pmap, List.pmap_map, List.attachWith, List.map_pmap]
  exact congrArg List.prod (List.pmap_congr_left _ (fun a ha h₁ h₂ =>
    EdgeSubset.oddSignFn_transport e κ φ ⟨a, h₂⟩ h₁))

open Classical in
/-- The alternating evaluation of the odd list at a vertex is
preserved by transport: the in-flag order changes only by moving
whole pairs, and pair blocks move evenly. -/
theorem EdgeSubset.evalOdd_oddListAt_transport {W₁ W₂ : Fragment α}
    (e : W₁.Equiv W₂) {F : EdgeSubset W₁} {k ℓ : ℕ}
    (h : MixedFunctional k ℓ) (μ : Multiset (Fin k))
    {κ : F.TransitionSystem} (o : κ.Orientation)
    (φ : F.OddColouring ℓ) (v : W₁.Vertex) :
    h.evalOdd μ ((EdgeSubset.transport e F).oddListAt
        (EdgeSubset.TransitionSystem.Orientation.transport e o)
        (EdgeSubset.OddColouring.transport e φ) (e.vertexEquiv v)) =
      h.evalOdd μ (F.oddListAt o φ v) := by
  unfold EdgeSubset.oddListAt
  have hstep := perm_pmap Subtype.mk (F.inFlagsAt_transport_perm e o v)
    (fun _ hf => EdgeSubset.mem_of_mem_inFlagsAt hf)
    (fun _ hg => mem_transport_of_mem_map_inFlagsAt e hg)
  have h1 := h.evalOdd_flatMap_perm μ
    ((EdgeSubset.transport e F).oddPairFn (κ.transport e)
      (EdgeSubset.OddColouring.transport e φ))
    (fun _ => rfl) hstep []
  simp only [List.nil_append] at h1
  refine h1.trans ?_
  rw [List.pmap_map, List.attachWith]
  exact congrArg (h.evalOdd μ) (pmap_flatMap_congr _ _ _ _ _ _ _
    (fun a ha h₁ h₂ => EdgeSubset.oddPairFn_transport e κ φ ⟨a, h₂⟩ h₁))

/-- Transport of even colourings as an equivalence. -/
noncomputable def EdgeSubset.EvenColouring.transportEquiv
    {W₁ W₂ : Fragment α} (e : W₁.Equiv W₂) (F : EdgeSubset W₁)
    (k : ℕ) :
    F.EvenColouring k ≃ (EdgeSubset.transport e F).EvenColouring k where
  toFun := EdgeSubset.EvenColouring.transport e
  invFun ψ := ⟨fun f => ψ.val (EdgeSubset.transportComplEquiv e F f),
    fun f => by
      have harg : (EdgeSubset.transportComplEquiv e F
            ⟨W₁.pairing f.val, F.pairing_not_mem f.prop⟩).val =
          W₂.pairing (EdgeSubset.transportComplEquiv e F f).val := by
        show e.flagEquiv (W₁.pairing f.val) = W₂.pairing (e.flagEquiv f.val)
        exact e.pairing_comm f.val
      exact (congrArg ψ.val (Subtype.ext harg)).trans (ψ.prop _)⟩
  left_inv ψ := Subtype.ext (funext fun f => congrArg ψ.val
    (Equiv.symm_apply_apply _ _))
  right_inv ψ := Subtype.ext (funext fun f => congrArg ψ.val
    (Equiv.apply_symm_apply _ _))

/-- Transport of odd colourings as an equivalence. -/
noncomputable def EdgeSubset.OddColouring.transportEquiv
    {W₁ W₂ : Fragment α} (e : W₁.Equiv W₂) (F : EdgeSubset W₁)
    (ℓ : ℕ) :
    F.OddColouring ℓ ≃ (EdgeSubset.transport e F).OddColouring ℓ where
  toFun := EdgeSubset.OddColouring.transport e
  invFun φ := ⟨fun f => φ.val (EdgeSubset.transportFlagsEquiv e F f),
    fun f => by
      have harg : (EdgeSubset.transportFlagsEquiv e F
            ⟨W₁.pairing f.val, F.pairing_mem _ f.prop⟩).val =
          W₂.pairing (EdgeSubset.transportFlagsEquiv e F f).val := by
        show e.flagEquiv (W₁.pairing f.val) = W₂.pairing (e.flagEquiv f.val)
        exact e.pairing_comm f.val
      exact (congrArg φ.val (Subtype.ext harg)).trans (φ.prop _)⟩
  left_inv φ := Subtype.ext (funext fun f => congrArg φ.val
    (Equiv.symm_apply_apply _ _))
  right_inv φ := Subtype.ext (funext fun f => congrArg φ.val
    (Equiv.apply_symm_apply _ _))

open Classical in
/-- **Transport invariance of the Definition 5 summand**: the
summand of a transported edge subset with transported transition
system and orientation is the original summand. -/
theorem EdgeSubset.mixedSummand_transport {W₁ W₂ : Fragment α}
    (e : W₁.Equiv W₂) {F : EdgeSubset W₁} {k ℓ : ℕ}
    (h : MixedFunctional k ℓ) {κ : F.TransitionSystem}
    (o : κ.Orientation) :
    (EdgeSubset.transport e F).mixedSummand h
        (EdgeSubset.TransitionSystem.Orientation.transport e o) =
      F.mixedSummand h o := by
  unfold EdgeSubset.mixedSummand
  rw [EdgeSubset.TransitionSystem.transport_circuitCount]
  congr 1
  refine Fintype.sum_equiv
    (EdgeSubset.EvenColouring.transportEquiv e F k).symm _ _ (fun ψ => ?_)
  refine Fintype.sum_equiv
    (EdgeSubset.OddColouring.transportEquiv e F ℓ).symm _ _ (fun φ => ?_)
  refine Fintype.prod_equiv e.vertexEquiv.symm _ _ (fun v => ?_)
  obtain ⟨ψ₀, rfl⟩ : ∃ ψ₀,
      ψ = EdgeSubset.EvenColouring.transportEquiv e F k ψ₀ :=
    ⟨_, ((EdgeSubset.EvenColouring.transportEquiv e F k).apply_symm_apply
      ψ).symm⟩
  obtain ⟨φ₀, rfl⟩ : ∃ φ₀,
      φ = EdgeSubset.OddColouring.transportEquiv e F ℓ φ₀ :=
    ⟨_, ((EdgeSubset.OddColouring.transportEquiv e F ℓ).apply_symm_apply
      φ).symm⟩
  obtain ⟨v₀, rfl⟩ : ∃ v₀, v = e.vertexEquiv v₀ :=
    ⟨_, (Equiv.apply_symm_apply _ _).symm⟩
  simp only [Equiv.symm_apply_apply]
  rw [show EdgeSubset.EvenColouring.transportEquiv e F k ψ₀ =
      EdgeSubset.EvenColouring.transport e ψ₀ from rfl,
    show EdgeSubset.OddColouring.transportEquiv e F ℓ φ₀ =
      EdgeSubset.OddColouring.transport e φ₀ from rfl,
    EdgeSubset.oddSignAt_transport, EdgeSubset.evenColoursAt_transport,
    EdgeSubset.evalOdd_oddListAt_transport]

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

section CirclesOnly

private instance (c : ℕ) : IsEmpty (Fragment.circlesOnly c).Flag :=
  inferInstanceAs (IsEmpty Empty)

private instance (c : ℕ) : IsEmpty (Fragment.circlesOnly c).Vertex :=
  inferInstanceAs (IsEmpty Empty)

end CirclesOnly

/-- A parameter on closed fragments is a mixed partition function
when it is the Definition 5 value of some mixed functional. -/
def IsMixedPartitionFunction (f : ClosedFragment → ℂ) : Prop :=
  ∃ (k ℓ : ℕ) (h : MixedFunctional k ℓ),
    ∀ W : ClosedFragment, f W = mixedPartition h W

/-- The partner sign flips across the pairing. -/
theorem oddPartnerSign_oddPartner (ℓ : ℕ) (i : Fin (2 * ℓ)) :
    oddPartnerSign ℓ (oddPartner ℓ i) = -oddPartnerSign ℓ i := by
  unfold oddPartner oddPartnerSign
  by_cases h : i.val < ℓ
  · rw [dif_pos h, if_pos h,
      if_neg (show ¬ i.val + ℓ < ℓ by omega)]
    norm_num
  · have hi : i.val < 2 * ℓ := i.isLt
    rw [dif_neg h, if_neg h,
      if_pos (show i.val - ℓ < ℓ by omega)]

/-- The partner sign squares to one. -/
theorem oddPartnerSign_mul_self (ℓ : ℕ) (i : Fin (2 * ℓ)) :
    oddPartnerSign ℓ i * oddPartnerSign ℓ i = 1 := by
  unfold oddPartnerSign
  by_cases h : i.val < ℓ <;> simp [h]

end RS
