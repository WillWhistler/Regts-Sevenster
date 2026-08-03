import RS.Classical.Deligne.KeyLemmaData
import RS.Classical.Deligne.SplitMonHom
import RS.Classical.Deligne.SplitPairDef
import RS.Classical.Deligne.ChainBNonzero
import RS.Classical.Deligne.IndAllColim

/-!
# The Key Lemma, closed over the ind-completion

The splitting data of Deligne's Key Lemma (2.8), assembled from
the graded splitting algebra: the carrier is the ℤ-graded
chain algebra, the base enters in degree zero, the module and its
dual in degrees `±1`, the pair product two stages up the
degree-zero line, and the section identity is the advancement of
the seed.  Nonvanishing is the stage-detection argument of the
balanced line.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v

variable {C : Type v} [SmallCategory C] [MonoidalCategory C]
  [SymmetricCategory C] [Abelian C] [RigidCategory C]
  [MonoidalPreadditive C]

/-- Tensoring preserves integer-indexed coproducts in the
ind-category, by transport from the universe-sized discrete
shape. -/
instance tensorLeft_ind_preservesShapeInt (X : Ind C) :
    PreservesColimitsOfShape (Discrete ℤ) (tensorLeft X) :=
  preservesColimitsOfShape_of_equiv
    (Discrete.equivalence Equiv.ulift.{v}) _

/-- Tensoring preserves integer-indexed coproducts in the
ind-category, right-hand version. -/
instance tensorRight_ind_preservesShapeInt (X : Ind C) :
    PreservesColimitsOfShape (Discrete ℤ) (tensorRight X) :=
  preservesColimitsOfShape_of_equiv
    (Discrete.equivalence Equiv.ulift.{v}) _

variable [CategoryTheory.Linear ℂ (Ind C)]
  [MonoidalLinear ℂ (Ind C)]
variable (B : Ind C) [MonObj B] [IsCommMonObj B]
variable (N N' : Mod (Ind C) B)

/-- **The Key Lemma** (Deligne 2.8) over the ind-completion: a
duality datum with the zigzag laws, over a base whose symmetric
powers of the module never vanish, admits splitting data — the
graded splitting algebra with its degree-`±1` insertions. -/
theorem keyLemmaData_ind (d : ModDualityDatum B N N') :
    KeyLemmaDataStatement B d := by
  intro hz _ hS
  letI := chainBGrMonObj B N N' d
  exact ⟨{ carrier := chainBGr B N N' d
           monObj := chainBGrMonObj B N N' d
           comm := chainBGr_isCommMonObj B N N' d
           ofBase := splitOfBase B N N' d
           ofBase_monHom :=
             ⟨splitOfBase_unit B N N' d,
               splitOfBase_mul B N N' d⟩
           unit_ne_zero := chainBGrUnit_ne_zero B N N' d
             (chainBUnit_ne_zero B N N' d hz
               fun n => hS (n + 1))
           ins := splitIns B N N' d
           ins' := splitIns' B N N' d
           ins_linear := splitIns_linear B N N' d
           ins'_linear := splitIns'_linear B N N' d
           pairMul := splitPairMul B N N' d
           pairMul_def := modTensorπ_splitPairMul B N N' d
           delta_eq := Eq.trans (Category.assoc _ _ _).symm
             (copairUnit_splitPairMul B N N' d) }⟩

end RS
