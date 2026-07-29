import RS.Novel.Extraction.CoordIso
import RS.Novel.Extraction.CopairUnique

/-!
# The complete standard model

Transporting the snake identities along the standard-model
isomorphism, and the resulting complete §5.1–5.2 package: a super
vector space with a supersymmetric form and a rigid copairing is
isomorphic to a standard model by an isomorphism carrying the form
to `stdForm` *and the copairing to `stdCopair`*
(`exists_std_model`).

The transport itself is delegated to mathlib's
`exactPairingCongr`; its transported evaluation and coevaluation
are identified with the `tensorHom`-conjugated form and copairing
via `tensorHom_def'`, and the transported copairing is then pinned
by `stdCopair_unique`.
-/

noncomputable section

namespace RS

open CategoryTheory
open MonoidalCategory

/-- A form and copairing with the snake identities assemble into
an exact pairing. -/
@[instance_reducible]
def exactPairingOfSnake {V : SuperVect}
    (b : SuperVect.Hom (SuperVect.tensorObj V V) SuperVect.tensorUnit)
    (C : SuperVect.Hom SuperVect.tensorUnit (SuperVect.tensorObj V V))
    (h1 : V ◁ (show 𝟙_ SuperVect ⟶ V ⊗ V from C) ≫
        (α_ V V V).inv ≫
        (show V ⊗ V ⟶ 𝟙_ SuperVect from b) ▷ V =
        (ρ_ V).hom ≫ (λ_ V).inv)
    (h2 : (show 𝟙_ SuperVect ⟶ V ⊗ V from C) ▷ V ≫
        (α_ V V V).hom ≫
        V ◁ (show V ⊗ V ⟶ 𝟙_ SuperVect from b) =
        (λ_ V).hom ≫ (ρ_ V).inv) :
    ExactPairing V V where
  coevaluation' := C
  evaluation' := b
  coevaluation_evaluation' := h1
  evaluation_coevaluation' := h2

/-- **The complete standard model** (accompanying paper §5.1–5.2): a
super vector space with a supersymmetric form and a rigid
copairing is isomorphic to a standard model `stdSuper k ℓ`, by an
isomorphism carrying the form to the standard form and the
copairing to the standard copairing. -/
theorem exists_std_model {V : SuperVect}
    (b : SuperVect.Hom (SuperVect.tensorObj V V) SuperVect.tensorUnit)
    (C : SuperVect.Hom SuperVect.tensorUnit (SuperVect.tensorObj V V))
    (hb : SuperVect.Hom.comp b (SuperVect.koszulBraiding V V) = b)
    (h1 : V ◁ (show 𝟙_ SuperVect ⟶ V ⊗ V from C) ≫
        (α_ V V V).inv ≫
        (show V ⊗ V ⟶ 𝟙_ SuperVect from b) ▷ V =
        (ρ_ V).hom ≫ (λ_ V).inv)
    (h2 : (show 𝟙_ SuperVect ⟶ V ⊗ V from C) ▷ V ≫
        (α_ V V V).hom ≫
        V ◁ (show V ⊗ V ⟶ 𝟙_ SuperVect from b) =
        (λ_ V).hom ≫ (ρ_ V).inv) :
    ∃ (k ℓ : ℕ) (e : SuperVect.Hom (stdSuper k ℓ) V)
      (e' : SuperVect.Hom V (stdSuper k ℓ)),
      SuperVect.Hom.comp e' e = SuperVect.Hom.id (stdSuper k ℓ) ∧
      SuperVect.Hom.comp e e' = SuperVect.Hom.id V ∧
      SuperVect.Hom.comp b (SuperVect.tensorHom e e) = stdForm k ℓ ∧
      SuperVect.Hom.comp (SuperVect.tensorHom e' e') C =
        stdCopair k ℓ := by
  obtain ⟨k, ℓ, e, e', hinv1, hinv2, hform⟩ :=
    exists_std_iso b C hb h1 h2
  refine ⟨k, ℓ, e, e', hinv1, hinv2, hform, ?_⟩
  let eIso : stdSuper k ℓ ≅ V :=
    ⟨e, e', hinv1, hinv2⟩
  letI EPV : ExactPairing V V := exactPairingOfSnake b C h1 h2
  letI EP : ExactPairing (stdSuper k ℓ) (stdSuper k ℓ) :=
    exactPairingCongr eIso eIso
  have hev : (ε_ (stdSuper k ℓ) (stdSuper k ℓ)) =
      (show stdSuper k ℓ ⊗ stdSuper k ℓ ⟶ 𝟙_ SuperVect from
        stdForm k ℓ) := by
    show stdSuper k ℓ ◁ eIso.hom ≫
        (eIso.hom ▷ V ≫ (show V ⊗ V ⟶ 𝟙_ SuperVect from b)) = _
    rw [← Category.assoc, ← tensorHom_def' eIso.hom eIso.hom]
    exact hform
  have hcoev : (η_ (stdSuper k ℓ) (stdSuper k ℓ)) =
      (show 𝟙_ SuperVect ⟶ stdSuper k ℓ ⊗ stdSuper k ℓ from
        SuperVect.Hom.comp (SuperVect.tensorHom e' e') C) := by
    show ((show 𝟙_ SuperVect ⟶ V ⊗ V from C) ≫ V ◁ eIso.inv) ≫
        eIso.inv ▷ stdSuper k ℓ = _
    rw [Category.assoc, ← tensorHom_def' eIso.inv eIso.inv]
    rfl
  refine stdCopair_unique k ℓ
    (SuperVect.Hom.comp (SuperVect.tensorHom e' e') C) ?_ ?_
  · rw [← hev, ← hcoev]
    exact EP.coevaluation_evaluation'
  · rw [← hev, ← hcoev]
    exact EP.evaluation_coevaluation'

end RS
