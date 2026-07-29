import RS.Classical.Interfaces.DelignePackage
import RS.Classical.CatTheory.Growth

/-!
# Deligne's theorem on tensor categories

The one cited input of the development, stated as Deligne states it.

Deligne's Théorème 0.6: a tensor category over a field of
characteristic zero that is finitely ⊗-generated and of moderate
growth is ⊗-equivalent to the category of representations of an
affine supergroup scheme.  A *tensor category over `k`* (Deligne
§0.1, after Deligne–Milne) is an essentially small abelian
`k`-linear rigid symmetric monoidal category with `k`-bilinear
tensor product and `End 𝟙 = k`.  Here `k = ℂ`.

Hypothesis by hypothesis, against `DeligneTheoremStatement` below:

* essentially small — `[EssentiallySmall.{v} A]`;
* abelian, ℂ-linear, with ℂ-bilinear tensor product —
  `[Abelian A]`, `[Linear ℂ A]`, `[MonoidalPreadditive A]`,
  `[MonoidalLinear ℂ A]`;
* rigid symmetric monoidal — `[MonoidalCategory A]`,
  `[SymmetricCategory A]`, `[RigidCategory A]`;
* `End 𝟙 = ℂ` — `HasScalarUnit A`;
* finitely ⊗-generated — `∃ X, TensorGeneratedBy A X`, every object
  a subquotient of a finite biproduct of mixed tensor powers
  `X ^ ⊗ a ⊗ (Xᘁ) ^ ⊗ b`;
* moderate growth — `ModerateLengthGrowth A`, the length of
  `Y ^ ⊗ N` bounded by `C · c ^ N` for every object `Y`.

Exactness of the tensor product is not a separate field: rigidity
makes `X ⊗ −` both a left and a right adjoint, so it is exact.
`[HasFiniteBiproducts A]` is implied by `[Abelian A]`; it is named
only because the generation predicate needs the biproducts in order
to be stated, and so narrows nothing.

Two things are taken from the theorem rather than all of it, and
both make the assumption weaker than what Deligne proves.  Only one
direction of his equivalence is assumed — the one that produces a
functor.  And the conclusion is taken in fibre-functor form: a
⊗-equivalence with the representations of an affine supergroup
scheme yields an exact faithful ℂ-linear symmetric monoidal functor
to finite-dimensional super vector spaces by composing with the
forgetful functor, and that functor, `DeligneFibreFunctor`, is what
is assumed to exist.  Deligne notes that the finite-generation
hypothesis can be dispensed with, but does not write that reduction
down, so it is kept here as he states it.

The development consumes less again: only a symmetric monoidal
ℂ-linear functor to super vector spaces is used downstream, and
`DeligneFibreFunctor.toPackage` forgets faithfulness and exactness.

The growth hypothesis is where the form assumed here and the form
the envelope establishes differ.  The envelope bounds the
dimensions of the endomorphism algebras of the tensor powers; in a
semisimple category with finite-dimensional Hom-spaces that bounds
the lengths, which is what the theorem asks
(`moderateLengthGrowth_of_endGrowth`).  Semisimplicity and the
finite-dimensional Hom-spaces are properties of the envelope, used
there; they are not hypotheses of the theorem.

Reference: Pierre Deligne, *Catégories tensorielles*, Moscow Math.
J. **2** (2002), 227–248, Théorème 0.6 (with §0.1 for the
definitions); see also Victor Ostrik, *Tensor categories (after
P. Deligne)*, arXiv:math/0401347, Thm 2.3.
-/

namespace RS

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u v

/-- The conclusion of Deligne's theorem for a candidate tensor
category: an exact faithful ℂ-linear symmetric monoidal functor into
super vector spaces.  This extends the consumed interface
(`DelignePackage`) by the conclusions the development does not use:
faithfulness, and exactness in the form of preservation of finite
limits and finite colimits. -/
structure DeligneFibreFunctor (A : Type*) [Category A]
    [MonoidalCategory A] [SymmetricCategory A] [Preadditive A]
    [Linear ℂ A] where
  /-- The fibre functor. -/
  ω : A ⥤ SuperVect
  /-- The fibre functor is symmetric monoidal. -/
  braided : ω.Braided
  /-- The fibre functor is additive. -/
  additive : ω.Additive
  /-- The fibre functor is ℂ-linear. -/
  linear : ω.Linear ℂ
  /-- The fibre functor is faithful. -/
  faithful : ω.Faithful
  /-- The fibre functor preserves finite limits: the left half of
  exactness. -/
  preservesFiniteLimits : PreservesFiniteLimits ω
  /-- The fibre functor preserves finite colimits: the right half of
  exactness. -/
  preservesFiniteColimits : PreservesFiniteColimits ω

/-- Forgetting exactness and faithfulness of a Deligne fibre functor
leaves the structure the development consumes. -/
def DeligneFibreFunctor.toPackage {A : Type*} [Category A]
    [MonoidalCategory A] [SymmetricCategory A] [Preadditive A]
    [Linear ℂ A] (F : DeligneFibreFunctor A) : DelignePackage A where
  ω := F.ω
  braided := F.braided
  additive := F.additive
  linear := F.linear

/-- **Deligne's theorem** (Catégories tensorielles, Théorème 0.6):
every essentially small abelian ℂ-linear rigid symmetric monoidal
category with ℂ-bilinear tensor product, scalar unit endomorphisms,
a finite tensor generator and moderate growth of the lengths of its
tensor powers admits an exact faithful ℂ-linear symmetric monoidal
fibre functor to finite-dimensional super vector spaces. -/
def DeligneTheoremStatement : Prop :=
  ∀ (A : Type u) [Category.{v} A] [Abelian A] [Linear ℂ A]
    [MonoidalCategory A] [SymmetricCategory A]
    [MonoidalPreadditive A] [MonoidalLinear ℂ A]
    [HasFiniteBiproducts A] [RigidCategory A]
    [EssentiallySmall.{v} A],
    HasScalarUnit A →
    (∃ X : A, TensorGeneratedBy A X) →
    ModerateLengthGrowth A →
    Nonempty (DeligneFibreFunctor A)

end RS
