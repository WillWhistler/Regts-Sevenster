import RS.Novel.Skein.LoopExample
import RS.TheoremConverse
import RS.TheoremForward
import RS.TheoremQuant

/-!
# The statement surface, pinned

Reading a formalization means reading what its theorems *say*, and
that reduces to the handful of definitions their statements are
phrased in.  This module lists exactly those definitions and pins
each one's type, and then pins the type of every theorem of record.

For the development's own definitions this is a *signature* audit.
Each `#guard_msgs` turns a change to a pinned type into a compile
error, so nothing enters or leaves a summit statement unnoticed; but
a type is not a meaning, and a definition can be rewritten while
keeping it — `EdgeRankBounded` would still read
`(ClosedFragment → ℂ) → ℕ → Prop` whatever it bounded.  Reading the
summits therefore means reading the linked definitions, which is
what the file lists them for.  For the one definition where a
convention could silently be wrong — `mixedPartition`, which carries
the circuit sign, the Eulerian condition and the odd-colour
bookkeeping — the last section pins a value instead of a type.

The one statement the development *assumes* is held to a higher
standard, because nothing downstream can contradict it: the cited
input is pinned by content, and so is every predicate its hypothesis
list is phrased in.  `Blueprint.lean` and its parts then pin what
the summits depend on.

The definitions all live in `RS/Definitions.lean`, the
self-contained statement surface that the comparator certification
trusts and the rest of the tree imports.
-/

namespace RS

/-! ## The model

A fragment is a flag (half-edge) graph over a label type; a closed
fragment is one with no boundary labels, and `Fragment.Equiv` is
isomorphism of fragments. -/

/-- info: Fragment : Type → Type 1 -/
#guard_msgs in
#check @Fragment

/-- info: ClosedFragment : Type 1 -/
#guard_msgs in
#check @ClosedFragment

/-- info: emptyClosedFragment : ClosedFragment -/
#guard_msgs in
#check @emptyClosedFragment

/-- info: @Fragment.Equiv : {α : Type} → Fragment α → Fragment α → Type -/
#guard_msgs in
#check @Fragment.Equiv

/-! ## Mixed partition functions

`MixedFunctional k ℓ` is a vertex functional with `k` even and `2ℓ`
odd colours, `mixedPartition` is Definition 5 of Regts–Sevenster on
the flag model, and the two predicates say that a parameter is such
a partition function, with and without a bound on the dimensions. -/

/-- info: MixedFunctional : ℕ → ℕ → Type -/
#guard_msgs in
#check @MixedFunctional

/-- info: @mixedPartition : {α : Type} → {k ℓ : ℕ} → MixedFunctional k ℓ → Fragment α → ℂ -/
#guard_msgs in
#check @mixedPartition

/-- info: IsMixedPartitionFunction : (ClosedFragment → ℂ) → Prop -/
#guard_msgs in
#check @IsMixedPartitionFunction

/-- info: IsMixedPartitionFunctionBounded : (ClosedFragment → ℂ) → ℕ → Prop -/
#guard_msgs in
#check @IsMixedPartitionFunctionBounded

/-! ## Edge-connection rank

`EdgeRankBounded f R` says the connection pairings of `f` have rank
at most `R ^ t` at every arity `t`; `EdgeRankParameter R` packages a
normalized, isomorphism-invariant parameter with that bound. -/

/-- info: EdgeRankBounded : (ClosedFragment → ℂ) → ℕ → Prop -/
#guard_msgs in
#check @EdgeRankBounded

/-- info: EdgeRankParameter : ℕ → Type 1 -/
#guard_msgs in
#check @EdgeRankParameter

/-! ## The statements and the one cited input -/

/-- info: RegtsSevensterStatement : Prop -/
#guard_msgs in
#check @RegtsSevensterStatement

/-- info: RegtsSevensterStatementQuant : Prop -/
#guard_msgs in
#check @RegtsSevensterStatementQuant

/-- info: RegtsSevensterConverseStatement : Prop -/
#guard_msgs in
#check @RegtsSevensterConverseStatement

/-- info: DeligneTheoremStatement : Prop -/
#guard_msgs in
#check @DeligneTheoremStatement

/-! ### The cited input, unfolded

A type is not a meaning, so the one statement the development
assumes is pinned by content as well as by name: its hypothesis
list, and the definition of every predicate that list is phrased in.
An auditor compares what follows with Deligne's Théorème 0.6 and
§0.1; a change to any of it is a compile error.
-/

set_option pp.funBinderTypes true in
/--
info: def RS.HasScalarUnit.{v, u} : (A : Type u) →
  [inst : CategoryTheory.Category.{v, u} A] →
    [inst_1 : CategoryTheory.Preadditive A] →
      [CategoryTheory.Linear ℂ A] → [CategoryTheory.MonoidalCategory A] → Prop :=
fun (A : Type u) [CategoryTheory.Category.{v, u} A] [CategoryTheory.Preadditive A] [CategoryTheory.Linear ℂ A]
    [CategoryTheory.MonoidalCategory A] =>
  Function.Bijective fun (c : ℂ) =>
    c • CategoryTheory.CategoryStruct.id (CategoryTheory.MonoidalCategoryStruct.tensorUnit A)
-/
#guard_msgs in
#print HasScalarUnit

set_option pp.funBinderTypes true in
/--
info: tensorPow_zero : ∀ (A : Type u_2) [inst : CategoryTheory.Category.{u_1, u_2} A]
  [inst_1 : CategoryTheory.MonoidalCategory A] (X : A),
  tensorPow A X 0 = CategoryTheory.MonoidalCategoryStruct.tensorUnit A
-/
#guard_msgs in
#check @tensorPow_zero

set_option pp.funBinderTypes true in
/--
info: tensorPow_succ : ∀ (A : Type u_2) [inst : CategoryTheory.Category.{u_1, u_2} A]
  [inst_1 : CategoryTheory.MonoidalCategory A] (X : A) (n : ℕ),
  tensorPow A X (n + 1) = CategoryTheory.MonoidalCategoryStruct.tensorObj (tensorPow A X n) X
-/
#guard_msgs in
#check @tensorPow_succ

set_option pp.funBinderTypes true in
/--
info: def RS.mixedPow.{v, u} : (A : Type u) →
  [inst : CategoryTheory.Category.{v, u} A] →
    [inst_1 : CategoryTheory.MonoidalCategory A] → [CategoryTheory.RigidCategory A] → A → ℕ → ℕ → A :=
fun (A : Type u) [CategoryTheory.Category.{v, u} A] [CategoryTheory.MonoidalCategory A] [CategoryTheory.RigidCategory A]
    (X : A) (a b : ℕ) =>
  CategoryTheory.MonoidalCategoryStruct.tensorObj (tensorPow A X a) (tensorPow A Xᘁ b)
-/
#guard_msgs in
#print mixedPow

set_option pp.funBinderTypes true in
/--
info: def RS.IsSubquotientOf.{v, u} : {C : Type u} → [CategoryTheory.Category.{v, u} C] → C → C → Prop :=
fun {C : Type u} [CategoryTheory.Category.{v, u} C] (Y Z : C) =>
  ∃ (S : C) (i : S ⟶ Z) (p : S ⟶ Y), CategoryTheory.Mono i ∧ CategoryTheory.Epi p
-/
#guard_msgs in
#print IsSubquotientOf

set_option pp.funBinderTypes true in
/--
info: def RS.TensorGeneratedBy.{v, u} : (A : Type u) →
  [inst : CategoryTheory.Category.{v, u} A] →
    [inst_1 : CategoryTheory.MonoidalCategory A] →
      [inst_2 : CategoryTheory.Preadditive A] →
        [CategoryTheory.Limits.HasFiniteBiproducts A] → [CategoryTheory.RigidCategory A] → A → Prop :=
fun (A : Type u) [CategoryTheory.Category.{v, u} A] [CategoryTheory.MonoidalCategory A] [CategoryTheory.Preadditive A]
    [CategoryTheory.Limits.HasFiniteBiproducts A] [CategoryTheory.RigidCategory A] (X : A) =>
  ∀ (Y : A), ∃ (k : ℕ) (ab : Fin k → ℕ × ℕ), IsSubquotientOf Y (⨁ fun (t : Fin k) => mixedPow A X (ab t).1 (ab t).2)
-/
#guard_msgs in
#print TensorGeneratedBy

set_option pp.funBinderTypes true in
/--
info: def RS.LengthLE.{v, u} : {C : Type u} → [CategoryTheory.Category.{v, u} C] → C → ℕ → Prop :=
fun {C : Type u} [CategoryTheory.Category.{v, u} C] (Y : C) (k : ℕ) =>
  ∀ (f : Fin (k + 2) → CategoryTheory.Subobject Y), ¬StrictMono f
-/
#guard_msgs in
#print LengthLE

set_option pp.funBinderTypes true in
/--
info: def RS.ModerateLengthGrowth.{v, u} : (A : Type u) →
  [inst : CategoryTheory.Category.{v, u} A] → [CategoryTheory.MonoidalCategory A] → Prop :=
fun (A : Type u) [CategoryTheory.Category.{v, u} A] [CategoryTheory.MonoidalCategory A] =>
  ∀ (Y : A), ∃ (C : ℕ) (c : ℕ), ∀ (N : ℕ), LengthLE (tensorPow A Y N) (C * c ^ N)
-/
#guard_msgs in
#print ModerateLengthGrowth

set_option pp.funBinderTypes true in
/--
info: structure RS.DeligneFibreFunctor.{u_1, u_2} (A : Type u_1) [CategoryTheory.Category.{u_2, u_1} A]
  [CategoryTheory.MonoidalCategory A] [CategoryTheory.SymmetricCategory A] [CategoryTheory.Preadditive A]
  [CategoryTheory.Linear ℂ A] : Type (max (max 1 u_1) u_2)
number of parameters: 6
fields:
  RS.DeligneFibreFunctor.ω : CategoryTheory.Functor A SuperVect
  RS.DeligneFibreFunctor.braided : self.ω.Braided
  RS.DeligneFibreFunctor.additive : self.ω.Additive
  RS.DeligneFibreFunctor.linear : CategoryTheory.Functor.Linear ℂ self.ω
  RS.DeligneFibreFunctor.faithful : self.ω.Faithful
  RS.DeligneFibreFunctor.preservesFiniteLimits : CategoryTheory.Limits.PreservesFiniteLimits self.ω
  RS.DeligneFibreFunctor.preservesFiniteColimits : CategoryTheory.Limits.PreservesFiniteColimits self.ω
constructor:
  RS.DeligneFibreFunctor.mk.{u_1, u_2} {A : Type u_1} [CategoryTheory.Category.{u_2, u_1} A]
    [CategoryTheory.MonoidalCategory A] [CategoryTheory.SymmetricCategory A] [CategoryTheory.Preadditive A]
    [CategoryTheory.Linear ℂ A] (ω : CategoryTheory.Functor A SuperVect) (braided : ω.Braided) (additive : ω.Additive)
    (linear : CategoryTheory.Functor.Linear ℂ ω) (faithful : ω.Faithful)
    (preservesFiniteLimits : CategoryTheory.Limits.PreservesFiniteLimits ω)
    (preservesFiniteColimits : CategoryTheory.Limits.PreservesFiniteColimits ω) : DeligneFibreFunctor A
-/
#guard_msgs in
#print DeligneFibreFunctor

set_option pp.funBinderTypes true in
/--
info: def RS.DeligneTheoremStatement.{u, v} : Prop :=
∀ (A : Type u) [inst : CategoryTheory.Category.{v, u} A] [inst_1 : CategoryTheory.Abelian A]
  [inst_2 : CategoryTheory.Linear ℂ A] [inst_3 : CategoryTheory.MonoidalCategory A]
  [inst_4 : CategoryTheory.SymmetricCategory A] [inst_5 : CategoryTheory.MonoidalPreadditive A]
  [CategoryTheory.MonoidalLinear ℂ A] [inst_7 : CategoryTheory.Limits.HasFiniteBiproducts A]
  [inst_8 : CategoryTheory.RigidCategory A] [CategoryTheory.EssentiallySmall.{v, v, u} A],
  HasScalarUnit A → (∃ (X : A), TensorGeneratedBy A X) → ModerateLengthGrowth A → Nonempty (DeligneFibreFunctor A)
-/
#guard_msgs in
#print DeligneTheoremStatement

/-! ## The theorems of record

The converse carries no hypothesis; the forward direction and the
characterization carry Deligne's theorem and nothing else. -/

/-- info: regts_sevenster_converse : RegtsSevensterConverseStatement -/
#guard_msgs in
#check @regts_sevenster_converse

/-- info: regts_sevenster_deligne_only : DeligneTheoremStatement → RegtsSevensterStatement -/
#guard_msgs in
#check @regts_sevenster_deligne_only

/--
info: regts_sevenster_quant_deligne_only : DeligneTheoremStatement → RegtsSevensterStatementQuant
-/
#guard_msgs in
#check @regts_sevenster_quant_deligne_only

/--
info: @edgeRankBounded_of_mixedBounded : ∀ {f : ClosedFragment → ℂ} {B : ℕ},
  IsMixedPartitionFunctionBounded f B → EdgeRankBounded f (max 1 (2 * B))
-/
#guard_msgs in
#check @edgeRankBounded_of_mixedBounded

/--
info: regts_sevenster_iff : DeligneTheoremStatement →
  ∀ (f : ClosedFragment → ℂ),
    f emptyClosedFragment = 1 →
      (∀ (W₁ W₂ : ClosedFragment) (a : Fragment.Equiv W₁ W₂), f W₁ = f W₂) →
        ((∃ R, EdgeRankBounded f R) ↔ IsMixedPartitionFunction f)
-/
#guard_msgs in
#check @regts_sevenster_iff

/--
info: regts_sevenster_quant_roundtrip : DeligneTheoremStatement →
  ∀ (f : ClosedFragment → ℂ),
    f emptyClosedFragment = 1 →
      (∀ (W₁ W₂ : ClosedFragment) (a : Fragment.Equiv W₁ W₂), f W₁ = f W₂) →
        (∀ (R : ℕ), EdgeRankBounded f R → IsMixedPartitionFunctionBounded f ⌊2 * Real.exp 1 * ↑R⌋₊) ∧
          ∀ (B : ℕ), IsMixedPartitionFunctionBounded f B → EdgeRankBounded f (max 1 (2 * B))
-/
#guard_msgs in
#check @regts_sevenster_quant_roundtrip

/-! ## The definition, evaluated

A pinned type says nothing about a convention, and `mixedPartition`
is where the conventions are: the circuit sign, the Eulerian
condition, a loop's two incidences at its vertex, the difference
between a loop and a free circle, and the `η`-convention through
which distinct odd colourings reach a common basis vector.

The accompanying paper's worked example fixes all five at once.
Against the functional `charPolyFunctional θ`, whose mixed partition
function is the characteristic polynomial `det(θ I − A_G)` on graphs
without free circles, the one-vertex one-loop graph has `A_L = (2)`
and so must evaluate to `θ − 2`.  It does
(`RS/Novel/Skein/LoopExample.lean`); a sign error in any one of the
five would change the number.  Adjoining a free circle sends the
same functional to `0`, since `k − 2ℓ = 0` here — the same graph,
worth `θ − 2` with a loop and `0` with a circle. -/

/-- info: loopGraph : ClosedFragment -/
#guard_msgs in
#check @loopGraph

/-- info: charPolyFunctional : ℂ → MixedFunctional 2 1 -/
#guard_msgs in
#check @charPolyFunctional

/-- info: mixedPartition_loopGraph : ∀ (θ : ℂ), mixedPartition (charPolyFunctional θ) loopGraph = θ - 2 -/
#guard_msgs in
#check @mixedPartition_loopGraph

/-- info: mixedPartition_loopGraphCircle : ∀ (θ : ℂ), mixedPartition (charPolyFunctional θ) loopGraphCircle = 0 -/
#guard_msgs in
#check @mixedPartition_loopGraphCircle

end RS
