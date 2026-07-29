import RS.Common.PermCongr
import RS.Novel.Skein.ConnectionRank

/-!
# Eulerian edge subsets and circuit data

The combinatorial substrate of the mixed partition function
(Regts–Sevenster arXiv:1807.04494, Definition 5) on the flag model:
pairing-closed flag subsets (edge subsets), vertex degrees within a
subset, the Eulerian condition, and circuit data.

Circuit data is encoded by a second involution: a *transition
system* on an edge subset `F` is a fixed-point-free involution `κ`
of the flags of `F` matching flags at common vertices.  Together
with the edge pairing `σ` this generates the circuit walks; the
walk permutation is the composition `κ ∘ σ`, each geometric circuit
of `n` edges carries exactly two `(κ ∘ σ)`-cycles of length `n`
(its two directions), and the circuit count of Definition 5 is half
the number of cycles of the walk permutation.
-/

namespace RS

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

/-- Edge subsets are determined by their flag sets. -/
@[ext]
theorem ext {F₁ F₂ : EdgeSubset W} (h : F₁.flags = F₂.flags) :
    F₁ = F₂ := by
  cases F₁; cases F₂; simpa using h

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

/-- Transport of edge subsets along a fragment equivalence. -/
noncomputable def transport {W₁ W₂ : Fragment α} (e : W₁.Equiv W₂) :
    EdgeSubset W₁ ≃ EdgeSubset W₂ where
  toFun F :=
    ⟨F.flags.map e.flagEquiv.toEmbedding, fun f hf => by
      rw [Finset.mem_map_equiv] at hf ⊢
      rw [show e.flagEquiv.symm (W₂.pairing f) =
          W₁.pairing (e.flagEquiv.symm f) from by
        apply e.flagEquiv.injective
        rw [Equiv.apply_symm_apply, e.pairing_comm,
          Equiv.apply_symm_apply]]
      exact F.pairing_mem _ hf⟩
  invFun F :=
    ⟨F.flags.map e.flagEquiv.symm.toEmbedding, fun f hf => by
      rw [Finset.mem_map_equiv] at hf ⊢
      rw [Equiv.symm_symm, show e.flagEquiv (W₁.pairing f) =
          W₂.pairing (e.flagEquiv f) from e.pairing_comm f]
      exact F.pairing_mem _ hf⟩
  left_inv F := by
    apply ext
    ext f
    simp [Finset.mem_map_equiv]
  right_inv F := by
    apply ext
    ext f
    simp [Finset.mem_map_equiv]

/-- Transport preserves degrees at transported vertices. -/
theorem transport_deg {W₁ W₂ : Fragment α} (e : W₁.Equiv W₂)
    (F : EdgeSubset W₁) (v : W₁.Vertex) :
    (transport e F).deg (e.vertexEquiv v) = F.deg v := by
  letI := Classical.decEq (W₂.Vertex ⊕ α)
  letI := Classical.decEq (W₁.Vertex ⊕ α)
  unfold deg
  rw [show (transport e F).flags = F.flags.map e.flagEquiv.toEmbedding
      from rfl,
    Finset.filter_map, Finset.card_map]
  congr 1
  apply Finset.filter_congr
  intro f _
  rw [Function.comp_apply, Equiv.coe_toEmbedding, e.attach_comm]
  rcases W₁.attach f with w | ℓ
  · simp [Sum.map, e.vertexEquiv.apply_eq_iff_eq]
  · simp [Sum.map]

/-- Transport preserves the Eulerian condition. -/
theorem transport_eulerian {W₁ W₂ : Fragment α} (e : W₁.Equiv W₂)
    (F : EdgeSubset W₁) :
    (transport e F).Eulerian ↔ F.Eulerian := by
  constructor <;> intro h v
  · have hv := h (e.vertexEquiv v)
    rwa [transport_deg] at hv
  · have hv := h (e.vertexEquiv.symm v)
    rw [← transport_deg e F (e.vertexEquiv.symm v),
      Equiv.apply_symm_apply] at hv
    exact hv

/-- Membership in a transported edge subset. -/
theorem mem_transport_iff {W₁ W₂ : Fragment α} (e : W₁.Equiv W₂)
    (F : EdgeSubset W₁) (f : W₂.Flag) :
    f ∈ (transport e F).flags ↔ e.flagEquiv.symm f ∈ F.flags := by
  rw [show (transport e F).flags = F.flags.map e.flagEquiv.toEmbedding
    from rfl]
  exact Finset.mem_map_equiv

/-- Transporting there and back along an equivalence is the
identity on edge subsets. -/
theorem transport_symm_transport {W₁ W₂ : Fragment α}
    (e : W₁.Equiv W₂) (F : EdgeSubset W₁) :
    transport e.symm (transport e F) = F := by
  ext f
  rw [mem_transport_iff, mem_transport_iff]
  show e.flagEquiv.symm (e.flagEquiv.symm.symm f) ∈ F.flags ↔ _
  rw [Equiv.symm_symm, Equiv.symm_apply_apply]

/-- Transport of a transition system along a fragment
equivalence: the conjugated matching. -/
noncomputable def TransitionSystem.transport {W₁ W₂ : Fragment α}
    (e : W₁.Equiv W₂) {F : EdgeSubset W₁} (κ : F.TransitionSystem) :
    (EdgeSubset.transport e F).TransitionSystem where
  match_ := fun f => e.flagEquiv (κ.match_ (e.flagEquiv.symm f))
  match_invol := fun f hf => by
    rw [Equiv.symm_apply_apply,
      κ.match_invol _ ((mem_transport_iff e F f).mp hf),
      Equiv.apply_symm_apply]
  match_ne := fun f hf h => by
    have := κ.match_ne _ ((mem_transport_iff e F f).mp hf)
    apply this
    have h2 := congrArg e.flagEquiv.symm h
    rwa [Equiv.symm_apply_apply] at h2
  match_mem := fun f hf => by
    rw [mem_transport_iff, Equiv.symm_apply_apply]
    exact κ.match_mem _ ((mem_transport_iff e F f).mp hf)
  match_vertex := fun f hf v hv => by
    have hmem := (mem_transport_iff e F f).mp hf
    obtain ⟨w, hw⟩ := κ.attach_internal _ hmem
    have hcomm := e.attach_comm (e.flagEquiv.symm f)
    rw [Equiv.apply_symm_apply, hw] at hcomm
    rw [hcomm] at hv
    have hwv : e.vertexEquiv w = v := by
      simpa using Sum.inl.inj hv
    have hmv := κ.match_vertex _ hmem w hw
    have hcomm2 := e.attach_comm (κ.match_ (e.flagEquiv.symm f))
    rw [hmv] at hcomm2
    rw [hcomm2]
    simp [hwv]
  attach_internal := fun f hf => by
    have hmem := (mem_transport_iff e F f).mp hf
    obtain ⟨w, hw⟩ := κ.attach_internal _ hmem
    refine ⟨e.vertexEquiv w, ?_⟩
    have hcomm := e.attach_comm (e.flagEquiv.symm f)
    rw [Equiv.apply_symm_apply, hw] at hcomm
    simpa using hcomm

/-- The flag equivalence restricted to a transported edge
subset. -/
noncomputable def transportFlagsEquiv {W₁ W₂ : Fragment α}
    (e : W₁.Equiv W₂) (F : EdgeSubset W₁) :
    {f : W₁.Flag // f ∈ F.flags} ≃
      {f : W₂.Flag // f ∈ (transport e F).flags} :=
  e.flagEquiv.subtypeEquiv (fun f => by
    rw [mem_transport_iff, Equiv.symm_apply_apply])

/-- The transported walk permutation is the transported walk. -/
theorem TransitionSystem.transport_walkPerm {W₁ W₂ : Fragment α}
    (e : W₁.Equiv W₂) {F : EdgeSubset W₁} (κ : F.TransitionSystem) :
    (κ.transport e).walkPerm =
      (transportFlagsEquiv e F).permCongr κ.walkPerm := by
  ext x
  show e.flagEquiv (κ.match_ (e.flagEquiv.symm (W₂.pairing x.val))) = _
  rw [show ((transportFlagsEquiv e F).permCongr κ.walkPerm x).val =
      e.flagEquiv (κ.match_ (W₁.pairing
        (e.flagEquiv.symm x.val))) from by
    simp only [Equiv.permCongr_apply, transportFlagsEquiv,
      Equiv.subtypeEquiv_apply, Equiv.subtypeEquiv_symm]
    rfl]
  refine congrArg e.flagEquiv (congrArg κ.match_ ?_)
  have hp := e.pairing_comm (e.flagEquiv.symm x.val)
  rw [Equiv.apply_symm_apply] at hp
  rw [← hp, Equiv.symm_apply_apply]

/-- Transport preserves the circuit count. -/
theorem TransitionSystem.transport_circuitCount {W₁ W₂ : Fragment α}
    (e : W₁.Equiv W₂) {F : EdgeSubset W₁} (κ : F.TransitionSystem) :
    (κ.transport e).circuitCount = κ.circuitCount := by
  unfold TransitionSystem.circuitCount
  rw [TransitionSystem.transport_walkPerm, cycleType_permCongr,
    card_fixedPoints_permCongr]

end EdgeSubset

/-- `pmap` respects permutations of the underlying list. -/
theorem perm_pmap {β γ : Type*} {p : β → Prop}
    (f : ∀ b, p b → γ) {l₁ l₂ : List β} (hp : l₁.Perm l₂) :
    ∀ (H₁ : ∀ b ∈ l₁, p b) (H₂ : ∀ b ∈ l₂, p b),
      (l₁.pmap f H₁).Perm (l₂.pmap f H₂) := by
  induction hp with
  | nil => exact fun _ _ => List.Perm.refl _
  | cons b _ ih => exact fun _ _ => List.Perm.cons _ (ih _ _)
  | swap x y l => exact fun _ _ => List.Perm.swap _ _ _
  | trans hp₁ _ ih₁ ih₂ =>
    exact fun H₁ H₂ =>
      (ih₁ H₁ (fun b hb => H₁ b (hp₁.mem_iff.mpr hb))).trans
        (ih₂ (fun b hb => H₁ b (hp₁.mem_iff.mpr hb)) H₂)

/-- Congruent proof-carrying maps followed by list-valued functions
give equal flattenings. -/
theorem pmap_flatMap_congr {β β₁ β₂ γ : Type*}
    {p₁ p₂ : β → Prop} (f₁ : ∀ b, p₁ b → β₁) (f₂ : ∀ b, p₂ b → β₂)
    (G₁ : β₁ → List γ) (G₂ : β₂ → List γ) (l : List β)
    (H₁ : ∀ b ∈ l, p₁ b) (H₂ : ∀ b ∈ l, p₂ b)
    (hpt : ∀ b ∈ l, ∀ h₁ h₂, G₁ (f₁ b h₁) = G₂ (f₂ b h₂)) :
    (l.pmap f₁ H₁).flatMap G₁ = (l.pmap f₂ H₂).flatMap G₂ := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.pmap, List.flatMap_cons]
    rw [hpt a List.mem_cons_self _ _,
      ih _ _ (fun b hb => hpt b (List.mem_cons_of_mem _ hb))]

end RS
