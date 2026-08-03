import RS.Classical.CatTheory.WhiskerAdditive
import RS.Classical.Deligne.ModTensor

/-!
# Vanishing transport through the module tensor product

The relative tensor product of modules vanishes when either
factor does: the projection from the ordinary tensor product is
epic, and the ordinary tensor product with a zero object is
zero.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  [SymmetricCategory D]
variable [Preadditive D] [MonoidalPreadditive D]
  [HasCoequalizers D]
variable (A : D) [MonObj A] [IsCommMonObj A]
variable (M N : Mod D A)

omit [IsCommMonObj A] in
/-- **The module tensor product of a zero module vanishes**,
left-factor version. -/
theorem isZero_modTensor_left (h : IsZero M.X) :
    IsZero (modTensor A M N) := by
  rw [IsZero.iff_id_eq_zero]
  have hπ : modTensorπ A M N = 0 :=
    (isZero_whiskerRight h N.X).eq_of_src _ _
  have := modTensor_hom_ext A M N
    (k := 𝟙 (modTensor A M N)) (l := 0)
  apply this
  rw [hπ, Limits.zero_comp, Limits.zero_comp]

end RS
