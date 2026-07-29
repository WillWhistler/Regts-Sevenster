# A proof of the Regts–Sevenster conjecture, formalized

[![CI](https://github.com/WillWhistler/Regts-Sevenster/actions/workflows/ci.yml/badge.svg)](https://github.com/WillWhistler/Regts-Sevenster/actions/workflows/ci.yml)

A Lean 4 formalization of the accompanying paper

> W. Whistler, *Mixed partition functions are exactly the graph
> parameters of exponentially bounded edge-connection rank*,
> [arXiv:XXXX.XXXXX](https://arxiv.org/abs/XXXX.XXXXX).

A copy is included at [`Paper/rstheorem.pdf`](Paper/rstheorem.pdf)
— the exact version whose numbering this tree matches
([arXiv:XXXX.XXXXXv1](https://arxiv.org/abs/XXXX.XXXXXv1)); the
arXiv page above is the paper's canonical home.

The paper proves a conjecture of Regts and Sevenster
(Ann. Inst. Henri Poincaré D 8 (2021) 179–200,
[doi:10.4171/aihpd/100](https://doi.org/10.4171/aihpd/100);
[arXiv:1807.04494](https://arxiv.org/abs/1807.04494)): a graph
parameter normalized at the empty graph has exponentially bounded
edge-connection rank if and only if it is a mixed partition
function. This development machine-checks both implications,
together with the paper's dimension bound `k, 2ℓ ≤ ⌊2eR⌋`, over
the flag (half-edge) model of multigraph fragments. Numbered
results below are the paper's — the Main Theorem, Theorem 4.8,
Corollary 4.10, Theorem A.1 — except those attributed to Regts and
Sevenster (RS21 below), whose Definition 5, Proposition 3,
Theorem 6, Lemma 11 and displayed equations are cited by their own
numbers, in the journal version's numbering. (The arXiv copy
numbers the displays (11)–(16) as (19)–(24), and numbers the
closing display of Theorem 6's proof, unnumbered in the journal,
as (25)–(26); the named results agree.)

Claude Fable 5, Claude Opus 5 and GPT-5.6 Sol Pro were used
extensively in the development and preparation of this work.
[formalization.yaml](formalization.yaml) reports how.

## The theorems

`RS/TheoremQuant.lean` proves the forward direction in its
quantitative form, conditional on Deligne's theorem alone:

    theorem regts_sevenster_quant_deligne_only
        (hDeligne : DeligneTheoremStatement.{1}) :
        RegtsSevensterStatementQuant

The converse — every mixed partition function has exponentially
bounded connection rank, base `max 1 (k + 2ℓ)` — is a theorem of
the development, with no hypothesis of its own
(`RS/TheoremConverse.lean`):

    theorem regts_sevenster_converse : RegtsSevensterConverseStatement

so the characterization of the Main Theorem, and its quantitative
round trip, rest on Deligne alone:

    theorem regts_sevenster_iff
        (hDeligne : DeligneTheoremStatement.{1})
        (f : ClosedFragment → ℂ)
        (hempty : f emptyClosedFragment = 1)
        (hiso : ∀ W₁ W₂, W₁.Equiv W₂ → f W₁ = f W₂) :
        (∃ R : ℕ, EdgeRankBounded f R) ↔ IsMixedPartitionFunction f

## The statements

`RS/StatementForward.lean` states the forward direction as a single
`Prop`:

    RegtsSevensterStatement : Prop :=
      ∀ (R : ℕ) (f : EdgeRankParameter R), IsMixedPartitionFunction f.val

`EdgeRankParameter` (`RS/Novel/Skein/ConnectionRank.lean`)
packages the hypothesis class — a parameter on closed fragments,
normalized at the empty graph, isomorphism-invariant, with
connection pairings of rank at most `R ^ t` at every arity.
`IsMixedPartitionFunction` (`RS/Novel/Skein/MixedPartition.lean`)
is Definition 5 of Regts–Sevenster on the flag model: the sum
over Eulerian edge subsets of circuit-signed colouring sums
against a `(k, 2ℓ)` vertex functional, with the
`(k − 2ℓ)^{circles}` free-circle convention.
`RS/StatementQuant.lean` adds the dimension bound of
Corollary 4.10, and `RS/StatementConverse.lean` states the
converse.

## Assumed and proved

The forward direction is conditional on exactly one cited input,
a single declaration in `RS/Classical/Interfaces/`:

* `DeligneTheoremStatement` — Deligne's theorem on tensor
  categories (Catégories tensorielles, Moscow Math. J. 2 (2002),
  Théorème 0.6, with §0.1 for the definitions; see also Ostrik,
  math/0401347, Thm 2.3), with his own hypotheses: an essentially
  small abelian ℂ-linear rigid symmetric monoidal category with
  ℂ-bilinear tensor product, `End 𝟙 = ℂ`, a finite tensor
  generator, and moderate growth of the lengths of its tensor
  powers. Exactness of `⊗` needs no hypothesis — rigidity makes
  `X ⊗ −` both a left and a right adjoint — and
  `HasFiniteBiproducts`, which is implied by abelianness, is named
  only so the generation predicate can be stated.

  Two things are taken from the theorem rather than all of it, each
  weakening the assumption: one direction of Deligne's equivalence,
  and the conclusion in fibre-functor form — an exact faithful
  ℂ-linear symmetric monoidal functor to finite-dimensional super
  vector spaces (`DeligneFibreFunctor`), which a ⊗-equivalence with
  the representations of an affine supergroup scheme yields by
  composing with the forgetful functor. The development then
  consumes less again: only the symmetric monoidal ℂ-linear functor
  is used, as `DelignePackage`, and `DeligneFibreFunctor.toPackage`
  forgets faithfulness and exactness.

All of Deligne's hypotheses are discharged in the development for
the concretely constructed envelope
`Env f = Karoubi (Mat_ (Karoubi (SkeinObj f)))`
(`RS/Novel/Envelope/EnvDelignePackage.lean`), and the resulting
fibre functor is restricted along the braided linear embedding
back to the skein category.

Everything else is proved, not assumed:

* the classical symmetric-group input (`SchurPackage`) is a
  theorem (`RS.schurPackage`,
  `RS/Classical/SchurTheory/Package.lean`): the Jacobi–Trudi
  character theory — Frobenius formula, orthonormality,
  irreducible realization with sign, block theory, branching, and
  square-dimension growth — constructed from Mathlib's linear
  algebra;
* Regts–Sevenster's Proposition 3 is a theorem in both sectors,
  closed (`eulerianIndependence`) and open (`pairedLedger`);
* the paper's quantitative trace-zeta theorem (Theorem A.1) is
  formalized in the appendix's own generality, carrying its own
  hypothesis and threshold — a real dimension bound `A`, *every*
  integer side `s > 2e√A`, and degrees at most `s − 1`. The
  appendix starts from a rigid symmetric ℂ-linear category with
  `End 𝟙 = ℂ` and an object `Z`, and derives the symmetric-group
  action on `Z ^ ⊗ n`, the propagation of vanishing, the traces and
  the Frobenius identity; that derivation is `objectFrobeniusTower`,
  so `traceZeta_rational_of_object` and its super-spectrum form hold
  for an arbitrary category-and-object pair
  (`RS/Novel/Envelope/ObjectTower.lean`). The same conclusions over
  the derived interface alone are
  `FrobeniusTower.traceZeta_rational_sharp`
  (`RS/Novel/Envelope/TraceZetaSharp.lean`), which the skein
  endomorphism algebras instantiate directly. The nilpotent-trace
  step of the main chain is proved by that appendix route
  (`RS/Novel/Envelope/NilpotentTrace.lean`); the Etingof–Penneys
  theorem cited in the paper's main text is not consumed anywhere in
  this development.

The dependency-exhibiting two-input form remains available:

    theorem regts_sevenster_conditional
        (hSchur   : Nonempty SchurPackage.{1})
        (hDeligne : DeligneTheoremStatement.{1}) :
        RegtsSevensterStatement

## Correspondence with the paper

Six things differ from the paper's presentation, each deliberately:

* **The connection rank is the dimension of a row span.** The paper
  defines the rank of the infinite connection matrix as the
  supremum of the ranks of its finite submatrices;
  `EdgeRankBounded` bounds instead the `Module.rank` of the range of
  the curried pairing, so no infinite-matrix rank is needed. The two
  readings are the same condition, and
  `edgeRankBounded_iff_submatrixRank` proves it — the general fact,
  that a row span has dimension at most `n` exactly when every
  finite submatrix has rank at most `n`, is
  `RS/Common/RowSpanRank.lean`.
* **The base of the bound may be any natural number.** The paper's
  hypothesis (H2) asks for an integer `R ≥ 1`. For the
  characterization this changes nothing: the bound weakens as the
  base grows (`EdgeRankBounded.mono`), so a parameter admitted at
  `R = 0` is admitted at `R = 1` already, and `∃ R` is the same
  condition either way. The *quantitative* statement is genuinely
  stronger for it, and deliberately so: at `R = 0` the displayed
  bound `⌊2eR⌋` is `0`, so `RegtsSevensterStatementQuant` asserts
  there that the functional has `k = 2ℓ = 0` — a case the paper does
  not state, and one the `R = 1` instance does not imply, since its
  bound is `⌊2e⌋ = 5`.
* **The vertex functional is presented in sorted colour order.**
  `MixedFunctional` assigns values to multisets of even colours
  and *sets* of odd colours, with antisymmetry supplied by the
  sorting-sign evaluator (`evalOdd`); the paper's κ-paired wedge
  presentation, and the dictionary between the two — including
  the parity twist that must not be carried across it — are the
  subject of the convention discussion in the paper's
  Section 5.4.
* **Composition is written applicatively.** `Fragment.compose F G`
  glues the last `t` labels of `F` to the first `t` of `G`; it is
  the paper's `G ∘ F` and Mathlib's diagrammatic `F ≫ G`.
* **The appendix's growth constant is unconstrained.** Appendix A
  fixes a real `A ≥ 1` in its growth hypothesis;
  `objectFrobeniusTower` and `traceZeta_rational_of_object` take any
  real `A` with `dim End(Z ^ ⊗ n) ≤ A ^ n`. It is a hypothesis, so
  admitting more values makes the Lean statement the stronger one,
  and the extra range is degenerate: below `1` the bound forces
  `End(Z ^ ⊗ n) = 0` for all large `n`.
* **The envelope is completed in two stages.** The paper's Cauchy
  completion is `𝒟_f = Kar(Add(𝒞_f))` (Section 3.4); the tree builds
  `Env f = Karoubi (Mat_ (Karoubi (SkeinObj f)))`, which is
  `Kar(Add(Kar(𝒞_f)))`. The inner Karoubi is where the atoms live:
  an atom is the image of an atomic idempotent of a skein
  endomorphism algebra, so it exists only once idempotents split,
  and the tree's nilpotent-trace argument for `Mat_` reads the
  atomic decomposition of each matrix entry
  (`AtomicIdempotents.lean`, `AtomDichotomy.lean`,
  `NilpotentMatTrace.lean`). Both categories are Cauchy completions
  of `𝒞_f` — idempotent-splitting before the additive envelope is
  undone by the outer Karoubi — so they are equivalent, and it is
  the one the tree builds for which Deligne's hypotheses are
  discharged.

`RS/Glossary.lean` glosses the recurring vocabulary — fragments,
transition systems, walk permutations, canonical frames — and
`ClassicalOverview.md` surveys the classical layer: the
literature results proved in the tree and the methods used.

## The converse route

The converse rests on one displayed identity, the closing display
of the proof of Regts–Sevenster's Theorem 6: the closure of two
fragments, evaluated by the mixed partition function, is the super
form of their two fragment tensors (`SuperGramIdentity`, proved as
`EdgeSubset.superGramIdentity`,
`RS/Novel/Skein/ConverseIdentity.lean`). The tensor is RS21's
`Σ_H t_h(F,H,ω_H,κ_H)`, with the fragment's own free circles
riding along (`fragmentTensor`, `RS/Novel/Skein/ConverseGram.lean`).

The route follows Regts–Sevenster §4 directly. Lemma 11 — the
sign of a permutation carrying one directed perfect matching to
another — is proved on `DirMatching`; the super form (11), the
normalised tensor `t_h`, and its invariance under reversing a
trail (12) are in `RS/Novel/Skein/RSTensor.lean`, together with
the pairing identity (13) and its vanishing across a mismatch
(16). The composition side is carried by a colouring recursion
over the interface (`RS/Novel/Skein/ColourGlue.lean`,
`EdgeTerm.lean`, `ColourRecursion.lean`) which writes the
closure's value on the two fragments' disjoint union, and by the
ledger recursion (`RS/Novel/Skein/LedgerRecursion.lean`) whose
(14) fuses the two fragments' circuit-and-matching signs into the
composition's. The Eulerian position RS21's step 1 asks for is
supplied by the composition's own orientation, which alternates
across every interface pair (`chainDir_pushData_alternates`,
`RS/Novel/Skein/InterfaceAlternate.lean`). The assembly of these
into the identity is `RS/Novel/Skein/ConverseAssembly.lean`.

A cut that closes turns its edge into a free circle, and the two
branches of that edge weigh `k` and `−2ℓ`
(`edgeTermAt_closedCut_false_row`,
`edgeTermAt_closedCut_true_row`). Summed over the interface
colourings, a base subset's whole summand is therefore the
composition's own term at the subset's image, times the free
circles the subset's own closing cuts contribute (`cutFactor`,
`edgeTermAt_pushData_colourSum`) — and that product is
choice-free at the closed top, so the base sum may be read with
the data each subset itself determines (`summandSum_bits_indep`,
`baseSumBitsOf_all`).

The open sector of Proposition 3 needs bookkeeping the closed one
does not: ordered cuts with a transposed symplectic factor,
low-to-high chain orientations, a Pfaffian chord sign, and
state-threaded transport. Each is forced — independence across
boundary pairings is false, and `not_throughIndependenceC`
exhibits two path-canonical data whose signed values differ, so
the value can only be a function of the chord diagram
(`pairedLedger`: the chord-signed canonical
value of an open fragment is a function of its boundary pairing
alone, the pairing-fibre holonomy being trivial).

## Auditing

Five kinds of front-door file carry the semantic and trust
surface — what the theorems say, and what they rest on:

* **The statements** — `RS/StatementForward.lean` (the forward
  direction), `RS/StatementQuant.lean` (its quantitative form),
  `RS/StatementConverse.lean` (the converse).
* **The vocabulary** — `RS/Glossary.lean`, and
  `ClassicalOverview.md` for the classical layer.
* **The theorems of record** — `RS/TheoremForward.lean`,
  `RS/TheoremQuant.lean`, `RS/TheoremConverse.lean`: each summit is a
  statement and a few lines.
* **The statement surface** —
  `RS/Assembly/BlueprintStatement.lean` collects every definition
  the summits are phrased in and pins its type, then pins the type
  of every theorem of record.
* **The axiom audits** — `RS/Assembly/Blueprint.lean` and its two
  parts.

The definitions those statements rest on are `Fragment` and
`Fragment.Equiv` (`RS/Novel/Skein/FlagGraph.lean`),
`ClosedFragment`, `emptyClosedFragment`, `EdgeRankBounded` and
`EdgeRankParameter` (`RS/Novel/Skein/ConnectionRank.lean`),
`MixedFunctional`, `mixedPartition` and
`IsMixedPartitionFunction` (`RS/Novel/Skein/MixedPartition.lean`),
`IsMixedPartitionFunctionBounded` (`RS/StatementQuant.lean`), and
the one cited input `DeligneTheoremStatement` together with the
`DeligneFibreFunctor` its conclusion names
(`RS/Classical/Interfaces/DeligneTheorem.lean`) — twelve in all.
`BlueprintStatement.lean` pins those twelve together with the three
named statements they are assembled into (`RegtsSevensterStatement`,
`RegtsSevensterStatementQuant`, `RegtsSevensterConverseStatement`),
fifteen types in all, and then the type of each of the six theorems
of record.

`RS/Assembly/Blueprint.lean` and its two parts pin the axiom set
of every main theorem with `#guard_msgs`-guarded `#print axioms`
lines, so drift from `[propext, Classical.choice, Quot.sound]` is
a compile error rather than a reading exercise. Both kinds of
audit are part of the default `lake build` target.

What the statement pins catch, for the development's own
definitions, is a change of *type*: a definition entering or leaving
a summit statement, or a theorem of record concluding something
else. A definition can still be rewritten while keeping its type.

One of them carries conventions a type cannot see —
`mixedPartition`, which reads the circuit sign, the Eulerian
condition, a loop's two incidences at its vertex, the difference
between a loop and a free circle, and the `η`-convention through
which distinct odd colourings reach a common basis vector. That
definition is pinned by a *value* as well. The paper's worked
example fixes the functional `h(θ)` whose mixed partition function
is `det(θ I − A_G)` on graphs without free circles; the one-vertex
one-loop graph has `A_L = (2)`, so it must evaluate to `θ − 2`, and
`mixedPartition_loopGraph` (`RS/Novel/Skein/LoopExample.lean`)
proves that it does. A sign error in any one of the five would
change the number.

The one statement the development *assumes* is pinned by content
instead — `DeligneTheoremStatement` unfolded, together with the
definition of every predicate its hypothesis list is phrased in
(`HasScalarUnit`, `TensorGeneratedBy` and the `IsSubquotientOf` and
`mixedPow` it is built from, `ModerateLengthGrowth` and its
`LengthLE`, and the `DeligneFibreFunctor` it concludes with). An
auditor compares that block with Deligne's Théorème 0.6 and §0.1,
and any drift in it is a compile error.

## Certification

Beyond the in-tree audits, the repository carries an independent
certification surface for
[comparator](https://github.com/leanprover/comparator):
`Challenge.lean` states the six theorems of record with `sorry`,
importing only the statement modules; `Solution.lean` proves each by
the theorem of record of the same name; and
`comparator-config.json` lists the six names and the axiom
whitelist. Comparator builds the two modules separately, confirms
at the kernel-export level — independently of the elaborator — that
each solution proves exactly the challenged statement, checks the
proofs against `[propext, Classical.choice, Quot.sound]`, and
replays them through the kernel. The CI workflow
(`.github/workflows/ci.yml`) runs the build, the audits, the
environment linters and the certification on every push.

## Building

The tree pins Lean `v4.31.0` and Mathlib at its `v4.31.0` release
tag, so it builds from a clean clone:

    lake exe cache get      # Mathlib's prebuilt oleans
    lake build              # green, zero warnings

Budget around 12 GB of disk: roughly 8.5 GB for Mathlib and its
dependencies, source and oleans, and 3 GB for this tree's own build
products. Once the cache is in place, a clean build of all 476
modules of the tree takes about five minutes on 128 hardware
threads; the wall time is dominated by the longest import chain, so
expect appreciably more on a small machine. Verifying the audits and
the summits:

    lake env lean RS/Assembly/BlueprintStatement.lean
    lake env lean RS/Assembly/Blueprint.lean
    lake env lean RS/Assembly/BlueprintConverse.lean
    lake env lean RS/Assembly/BlueprintSchur.lean

Each is silent on success. The tree carries no `sorry`, no custom
`axiom`, and no `native_decide`, and

    lake exe runLinter RS

reports `Linting passed for RS` — the Batteries linter suite, run
over every declaration in the tree, at zero findings.

## Provenance

[formalization.yaml](formalization.yaml) reports, in the
[mathlib-initiative](https://github.com/mathlib-initiative/formalization.yaml)
schema, what was formalized, how it was produced, where it diverges
from the paper, and how the paper's numbered results map to
declarations of the tree. [CITATION.cff](CITATION.cff) is the
citation metadata.

## Licence

Apache License 2.0; see [LICENSE](LICENSE). The paper in
`Paper/` is distributed under
[CC BY 4.0](https://creativecommons.org/licenses/by/4.0/), not
the repository licence.
