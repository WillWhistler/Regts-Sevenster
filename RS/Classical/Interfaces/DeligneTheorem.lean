import RS.Definitions
import RS.Classical.Interfaces.DelignePackage
import RS.Classical.CatTheory.Growth

/-!
# Deligne's theorem on tensor categories

The one cited input of the development — `DeligneTheoremStatement`,
carrying Deligne's own hypotheses, with `DeligneFibreFunctor` as its
conclusion — is stated in `RS/Definitions.lean`, together with a
hypothesis-by-hypothesis correspondence against Théorème 0.6 and
§0.1 of *Catégories tensorielles* (Moscow Math. J. **2** (2002),
227–248; see also Ostrik, arXiv:math/0401347, Thm 2.3).

This module carries the step from the conclusion to the consumed
interface: `DeligneFibreFunctor.toPackage` forgets faithfulness and
exactness, leaving the symmetric monoidal ℂ-linear functor the
development uses (`DelignePackage`).  Both weakenings — one
direction of Deligne's equivalence, and the fibre-functor form of
its conclusion — make the assumption weaker than what Deligne
proves.
-/

namespace RS

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u v

/-- Forgetting exactness and faithfulness of a Deligne fibre functor
leaves the structure the development consumes. -/
def DeligneFibreFunctor.toPackage {A : Type*} [Category A]
    [MonoidalCategory A] [SymmetricCategory A] [Preadditive A]
    [Linear ℂ A] (F : DeligneFibreFunctor A) : DelignePackage A where
  ω := F.ω
  braided := F.braided
  additive := F.additive
  linear := F.linear

end RS
