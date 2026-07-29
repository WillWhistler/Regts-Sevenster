import RS.Novel.Skein.PairingSignature
import RS.Novel.Skein.ChordSwapParity

/-!
# Boundary chord labels

The label of a boundary flag, extraction lemmas, and the crossing
relation rewritten as an order condition on the four labels — the
concrete bridge from `chordCrossingCount` to the abstract chord
parity layer.
-/

namespace RS

open scoped Classical

variable {α : Type} [LinearOrder α] {W : Fragment α}
  {F : EdgeSubset W}

namespace EdgeSubset

/-- The boundary label of a boundary flag. -/
noncomputable def boundaryLabel (F : EdgeSubset W) {f : W.Flag}
    (hf : f ∈ F.boundaryFlags) : α :=
  Classical.choose (F.attach_boundary_of_mem hf)

omit [LinearOrder α] in
/-- The defining equation of the boundary label. -/
theorem attach_boundaryLabel {f : W.Flag}
    (hf : f ∈ F.boundaryFlags) :
    W.attach f = Sum.inr (F.boundaryLabel hf) :=
  Classical.choose_spec (F.attach_boundary_of_mem hf)

omit [LinearOrder α] in
/-- The label determines the attachment. -/
theorem boundaryLabel_eq_of_attach {f : W.Flag} {i : α}
    (hf : f ∈ F.boundaryFlags) (h : W.attach f = Sum.inr i) :
    F.boundaryLabel hf = i :=
  Sum.inr.inj ((attach_boundaryLabel hf).symm.trans h)

omit [LinearOrder α] in
/-- **A boundary flag is the flag of its own label.** -/
theorem boundaryFlag_boundaryLabel {f : W.Flag} {F : EdgeSubset W}
    (hf : f ∈ F.boundaryFlags) :
    W.boundaryFlag (F.boundaryLabel hf) = f :=
  (W.eq_boundaryFlag (F.boundaryLabel hf) f
    (EdgeSubset.attach_boundaryLabel hf)).symm

omit [LinearOrder α] in
/-- Distinct boundary flags carry distinct labels. -/
theorem boundaryLabel_inj {f g : W.Flag}
    (hf : f ∈ F.boundaryFlags) (hg : g ∈ F.boundaryFlags)
    (h : F.boundaryLabel hf = F.boundaryLabel hg) : f = g := by
  have h1 := W.eq_boundaryFlag (F.boundaryLabel hf) f
    (attach_boundaryLabel hf)
  have h2 := W.eq_boundaryFlag (F.boundaryLabel hg) g
    (attach_boundaryLabel hg)
  rw [h1, h2, h]

omit [LinearOrder α] in
/-- The boundary label does not depend on the membership proof. -/
theorem boundaryLabel_congr {f g : W.Flag}
    (hf : f ∈ F.boundaryFlags) (hg : g ∈ F.boundaryFlags)
    (h : f = g) : F.boundaryLabel hf = F.boundaryLabel hg := by
  subst h
  rfl

variable {κ : F.RelTransitionSystem}

/-- **The crossing relation on labels**: `ChordCross` is exactly
the four-label interleaving condition (each chord low-to-high, the
first chord starting first). -/
theorem chordCross_iff_labels
    (b b' : {x : W.Flag // x ∈ F.boundaryFlags}) :
    ChordCross κ b b' ↔
      (F.boundaryLabel b.prop <
          F.boundaryLabel (κ.pathMatch_mem b.prop) ∧
        F.boundaryLabel b'.prop <
          F.boundaryLabel (κ.pathMatch_mem b'.prop) ∧
        F.boundaryLabel b.prop < F.boundaryLabel b'.prop ∧
        F.boundaryLabel b'.prop <
          F.boundaryLabel (κ.pathMatch_mem b.prop) ∧
        F.boundaryLabel (κ.pathMatch_mem b.prop) <
          F.boundaryLabel (κ.pathMatch_mem b'.prop)) := by
  unfold ChordCross
  constructor
  · rintro ⟨i, j, i', j', hbi, hpj, hbi', hpj', h1, h2, h3, h4, h5⟩
    rw [boundaryLabel_eq_of_attach b.prop hbi,
      boundaryLabel_eq_of_attach (κ.pathMatch_mem b.prop) hpj,
      boundaryLabel_eq_of_attach b'.prop hbi',
      boundaryLabel_eq_of_attach (κ.pathMatch_mem b'.prop) hpj']
    exact ⟨h1, h2, h3, h4, h5⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨F.boundaryLabel b.prop,
      F.boundaryLabel (κ.pathMatch_mem b.prop),
      F.boundaryLabel b'.prop,
      F.boundaryLabel (κ.pathMatch_mem b'.prop),
      attach_boundaryLabel b.prop,
      attach_boundaryLabel (κ.pathMatch_mem b.prop),
      attach_boundaryLabel b'.prop,
      attach_boundaryLabel (κ.pathMatch_mem b'.prop),
      h1, h2, h3, h4, h5⟩

end EdgeSubset

/-- Expansion of a sum over a four-element finset literal. -/
theorem sum_quad {β : Type} [DecidableEq β] {x y z w : β}
    (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w)
    (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w) (f : β → ℕ) :
    ∑ t ∈ ({x, y, z, w} : Finset β), f t =
      f x + (f y + (f z + f w)) := by
  rw [Finset.sum_insert (by simp [hxy, hxz, hxw]),
    Finset.sum_insert (by simp [hyz, hyw]),
    Finset.sum_insert (by simp [hzw]),
    Finset.sum_singleton]

end RS
