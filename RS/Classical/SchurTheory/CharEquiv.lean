import RS.Classical.SchurTheory.NativeTable

/-!
# Character invariance under representation equivalence

The character of a representation is invariant under equivalence:
two equivalent representations have the same character at every
group element.  The corollary specialises this to the native
submodule representations `rhoS`.
-/

namespace RS

open Finset LinearMap

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

omit [Fintype G] [DecidableEq G] in
/-- Equivalent representations have the same character. -/
theorem character_of_equiv {V W : Type*}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (e : ρ.Equiv σ) (g : G) :
    ρ.character g = σ.character g :=
  congr_fun (Representation.char_iso e) g

omit [DecidableEq G] in
/-- Equivalent native representations have the same native
character. -/
theorem nChar_of_equiv {S T : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G)}
    (e : (rhoS S).Equiv (rhoS T)) (g : G) :
    nChar S g = nChar T g := by
  unfold nChar
  exact character_of_equiv e g

end RS
