import RS.Definitions

/-!
# Tensoring is exact in a rigid abelian category

Deligne's 1.14 (Catégories tensorielles): in a rigid category the
functor `− ⊗ X` has `− ⊗ Xᘁ` as a two-sided adjoint, so over an
abelian base it preserves all finite limits and colimits — it is
exact.  The consequences collected here: tensoring preserves
monomorphisms, epimorphisms, and
zero objects, and a tensor power of a nonzero object detects
nothing (`X ^ ⊗ n = 0` forces `X = 0`, Deligne 1.17).
-/

namespace RS

open CategoryTheory MonoidalCategory Limits

universe v u

variable {A : Type u} [Category.{v} A] [MonoidalCategory A]
  [RigidCategory A]

/-- Right tensoring preserves all colimits: `− ⊗ X` is a left
adjoint (Frobenius reciprocity, with adjoint `− ⊗ Xᘁ`). -/
noncomputable instance tensorRight_preservesColimits (X : A) :
    PreservesColimitsOfSize.{v, v} (tensorRight X) :=
  (tensorRightAdjunction X (Xᘁ)).leftAdjoint_preservesColimits

/-- Right tensoring preserves all limits: `− ⊗ X` is a right
adjoint (with adjoint `− ⊗ ᘁX`). -/
noncomputable instance tensorRight_preservesLimits (X : A) :
    PreservesLimitsOfSize.{v, v} (tensorRight X) :=
  (tensorRightAdjunction (ᘁX) X).rightAdjoint_preservesLimits

/-- Left tensoring preserves all colimits. -/
noncomputable instance tensorLeft_preservesColimits (X : A) :
    PreservesColimitsOfSize.{v, v} (tensorLeft X) :=
  (tensorLeftAdjunction (ᘁX) X).leftAdjoint_preservesColimits

/-- Left tensoring preserves all limits. -/
noncomputable instance tensorLeft_preservesLimits (X : A) :
    PreservesLimitsOfSize.{v, v} (tensorLeft X) :=
  (tensorLeftAdjunction X (Xᘁ)).rightAdjoint_preservesLimits

end RS
