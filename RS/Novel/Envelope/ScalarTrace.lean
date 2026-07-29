import RS.Classical.CatTheory.Trace
import RS.Classical.CatTheory.LinearCategory

/-!
# The trace as a complex number

The categorical trace lands in `End (𝟙_ C)`, the endomorphisms of
the tensor unit.  When those are exactly the scalars — the
hypothesis `HasScalarUnit` — that monoid is ℂ, and the trace becomes
an honest complex-valued linear functional, which is what a tower's
trace fields ask for.

Cyclicity carries across the identification unchanged.
-/

namespace RS

open CategoryTheory MonoidalCategory

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C]

/-- **The unit's endomorphisms are the scalars**, as an algebra
isomorphism.  This is `HasScalarUnit` read as bijectivity of the
structure map. -/
noncomputable def unitScalarEquiv (h : HasScalarUnit C) :
    ℂ ≃ₐ[ℂ] End (𝟙_ C) :=
  AlgEquiv.ofBijective (Algebra.ofId ℂ (End (𝟙_ C))) h

/-- **The scalar named by an endomorphism of the unit.** -/
noncomputable def unitScalar (h : HasScalarUnit C) :
    End (𝟙_ C) →ₐ[ℂ] ℂ :=
  (unitScalarEquiv h).symm

/-! ## The complex-valued trace -/

variable [SymmetricCategory C] [MonoidalPreadditive C]
  [MonoidalLinear ℂ C] [RigidCategory C]

/-- **The complex-valued categorical trace.** -/
noncomputable def scalarTrace (h : HasScalarUnit C) (X : C) :
    End X →ₗ[ℂ] ℂ :=
  (unitScalar h).toLinearMap.comp (catTraceLin X)

/-- The complex-valued trace is cyclic. -/
theorem scalarTrace_comp_comm (h : HasScalarUnit C) {X Y : C}
    (f : X ⟶ Y) (g : Y ⟶ X) :
    scalarTrace h X (f ≫ g) = scalarTrace h Y (g ≫ f) := by
  show unitScalar h (catTrace (f ≫ g)) = unitScalar h (catTrace (g ≫ f))
  rw [catTrace_comp_comm]

end RS
