import RS.Classical.Deligne.IndCoeq
import RS.Classical.Deligne.CoprodPreserve

/-!
# The ind tensor preserves all small colimits

Combining the finite-colimit half (`IndCoeq`), the filtered half
(`IndTensorExact`) and the preservation of coproducts from finite
and filtered (`CoprodPreserve`): tensoring on either side in the
ind-category preserves every small colimit.  This is the form in
which the coend presentations of §3 pass through the tensor
product.
-/

namespace RS

open CategoryTheory Limits MonoidalCategory

universe v

variable {C : Type v} [SmallCategory C] [MonoidalCategory C]
variable [Abelian C] [RigidCategory C] [MonoidalPreadditive C]

instance tensorLeft_ind_preservesShapeDiscrete (A : Ind C)
    (α : Type v) :
    PreservesColimitsOfShape (Discrete α) (tensorLeft A) :=
  preservesColimitsOfShape_discrete_of_finite_and_filtered
    (tensorLeft A)

instance tensorRight_ind_preservesShapeDiscrete (A : Ind C)
    (α : Type v) :
    PreservesColimitsOfShape (Discrete α) (tensorRight A) :=
  preservesColimitsOfShape_discrete_of_finite_and_filtered
    (tensorRight A)

/-- **Tensoring preserves all small colimits in the
ind-category**, left-hand version. -/
instance tensorLeft_ind_preservesColimits (A : Ind C) :
    PreservesColimitsOfSize.{v, v} (tensorLeft A) :=
  preservesColimits_of_preservesCoequalizers_and_coproducts
    (tensorLeft A)

/-- **Tensoring preserves all small colimits in the
ind-category**, right-hand version. -/
instance tensorRight_ind_preservesColimits (A : Ind C) :
    PreservesColimitsOfSize.{v, v} (tensorRight A) :=
  preservesColimits_of_preservesCoequalizers_and_coproducts
    (tensorRight A)

end RS
