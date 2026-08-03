import RS.Classical.Deligne.FibreAdditive
import RS.Classical.Deligne.FibreMonoidal

/-!
# The two presentations of the fibre functor agree

Base change followed by realization was built twice: once directly,
so that additivity could be proved without an additive structure on
the module objects, and once as a composite, so that the monoidal
comparison could be read off.  The two are the same functor.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits

universe v u

section

variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
variable [SymmetricCategory D] [Preadditive D] [MonoidalPreadditive D]
variable [Linear ℂ D] [MonoidalLinear ℂ D]
variable (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R]

/-- **The direct and composite presentations of the fibre functor
agree.** -/
theorem fibreFun_eq_fibreOver : fibreFun L R = fibreOver L R := rfl

/-- The composite presentation is additive. -/
instance fibreOver_additive : (fibreOver L R).Additive :=
  fibreFun_eq_fibreOver L R ▸ fibreFun_additive L R

end

end RS
