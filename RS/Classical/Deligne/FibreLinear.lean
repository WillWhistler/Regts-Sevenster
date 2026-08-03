import RS.Classical.Deligne.PointFibre

/-!
# The fibre functor is complex-linear

The fibre functor is built by whiskering with the algebra and
composing, and both operations are complex-linear, so the functor
is.  This is the last field of `RS.DeligneFibreFunctor` that the
fibre construction does not supply on its own.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

section

variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
variable [SymmetricCategory D] [Preadditive D] [MonoidalPreadditive D]
variable [Linear ℂ D] [MonoidalLinear ℂ D]
variable (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R]

/-- **The fibre functor is complex-linear.** -/
instance fibreFun_linear : (fibreFun L R).Linear ℂ where
  map_smul {V W} f c := by
    rw [fibreFun_map, fibreFun_map]
    refine SuperCommAlgebra.Mod.Hom.ext ?_ ?_ <;>
      refine LinearMap.ext fun m => ?_
    · show m ≫ (R ◁ (c • f)) = c • (m ≫ (R ◁ f))
      rw [MonoidalLinear.whiskerLeft_smul]
      exact CategoryTheory.Linear.comp_smul _ _ _ m c (R ◁ f)
    · show m ≫ (R ◁ (c • f)) = c • (m ≫ (R ◁ f))
      rw [MonoidalLinear.whiskerLeft_smul]
      exact CategoryTheory.Linear.comp_smul _ _ _ m c (R ◁ f)

end

end RS
