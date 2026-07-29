import RS.Classical.CatTheory.Length

/-!
# Tensor powers of an object

The iterated tensor power `X ^ ⊗ n`, bracketed to the left, together
with the condition that a single object tensor-generates.  The
growth conditions stated in terms of tensor powers are in
`Growth.lean`.
-/

namespace RS

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe v u

variable (A : Type u) [Category.{v} A] [MonoidalCategory A]

/-- Iterated tensor power of an object. -/
def tensorPow (X : A) : ℕ → A
  | 0 => 𝟙_ A
  | n + 1 => tensorObj (tensorPow X n) X

/-- The empty tensor power is the unit. -/
theorem tensorPow_zero (X : A) : tensorPow A X 0 = 𝟙_ A := rfl

/-- `X ^ ⊗ (n + 1)` is `X ^ ⊗ n ⊗ X`.  Together with
`tensorPow_zero` this is the defining recursion. -/
theorem tensorPow_succ (X : A) (n : ℕ) :
    tensorPow A X (n + 1) = tensorPow A X n ⊗ X := rfl

/-- A mixed tensor power of `X`: `X ^ ⊗ a ⊗ (Xᘁ) ^ ⊗ b`. -/
def mixedPow [RigidCategory A] (X : A) (a b : ℕ) : A :=
  tensorPow A X a ⊗ tensorPow A (Xᘁ) b

/-- **Finite tensor generation**, in the sense of Deligne's
hypothesis: every object is a subquotient of a finite biproduct of
mixed tensor powers of `X` — a quotient of a subobject of such a
biproduct. -/
def TensorGeneratedBy [Preadditive A] [HasFiniteBiproducts A]
    [RigidCategory A] (X : A) : Prop :=
  ∀ Y : A, ∃ (k : ℕ) (ab : Fin k → ℕ × ℕ),
    IsSubquotientOf Y (⨁ fun t => mixedPow A X (ab t).1 (ab t).2)

/-- **Generation by retracts of pure powers**: every object is a
retract of a finite biproduct of tensor powers of `X` alone.  This
is how the envelope generates, and it is stronger than Deligne's
hypothesis in two ways at once — a retract rather than a
subquotient, and no duals among the powers. -/
def RetractGeneratedBy [Preadditive A] [HasFiniteBiproducts A]
    (X : A) : Prop :=
  ∀ Y : A, ∃ (k : ℕ) (ns : Fin k → ℕ)
    (ι : Y ⟶ ⨁ fun i => tensorPow A X (ns i))
    (π : (⨁ fun i => tensorPow A X (ns i)) ⟶ Y),
    ι ≫ π = 𝟙 Y

/-- A pure tensor power is the mixed power with no dual factors. -/
def tensorPowIsoMixed [RigidCategory A] (X : A) (n : ℕ) :
    tensorPow A X n ≅ mixedPow A X n 0 :=
  (ρ_ (tensorPow A X n)).symm

/-- **The retract formulation implies Deligne's.**  A splitting
`ι ≫ π = 𝟙` makes `ι` a split mono, hence a mono, and `Y` is a
quotient of itself, so a retract of a biproduct of pure powers is a
subquotient of the corresponding biproduct of mixed powers. -/
theorem tensorGeneratedBy_of_retract [Preadditive A]
    [HasFiniteBiproducts A] [RigidCategory A] {X : A}
    (h : RetractGeneratedBy A X) : TensorGeneratedBy A X := by
  intro Y
  obtain ⟨k, ns, ι, π, hιπ⟩ := h Y
  refine ⟨k, fun t => (ns t, 0),
    isSubquotientOf_of_retract
      (ι ≫ (biproduct.mapIso fun i => tensorPowIsoMixed A X (ns i)).hom)
      ((biproduct.mapIso fun i => tensorPowIsoMixed A X (ns i)).inv ≫ π)
      ?_⟩
  rw [Category.assoc, Iso.hom_inv_id_assoc, hιπ]

end RS
