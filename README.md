# A proof of the Regts–Sevenster conjecture, formalized

[![CI](https://github.com/WillWhistler/Regts-Sevenster/actions/workflows/ci.yml/badge.svg)](https://github.com/WillWhistler/Regts-Sevenster/actions/workflows/ci.yml)

A Lean 4 formalization of the accompanying paper

> W. Whistler, *Mixed partition functions are exactly the graph
> parameters of exponentially bounded edge-connection rank*,
> [arXiv:2607.27198](https://arxiv.org/abs/2607.27198).

A copy is included at [`Paper/rstheorem.pdf`](Paper/rstheorem.pdf)
— the text whose numbering this tree matches; the arXiv page above
is the paper's canonical home.

The paper proves a conjecture of Regts and Sevenster
(Ann. Inst. Henri Poincaré D 8 (2021) 179–200,
[doi:10.4171/aihpd/100](https://doi.org/10.4171/aihpd/100);
[arXiv:1807.04494](https://arxiv.org/abs/1807.04494)): a graph
parameter normalized at the empty graph has exponentially bounded
edge-connection rank if and only if it is a mixed partition
function. The paper's Main Theorem includes the sharp colour budget
`k + 2ℓ ≤ R`. This development machine-checks both implications
with that budget for natural rank bases, together with the even
connection-rank growth limit, minimum colour dimension, minimal
parity formulas and padding criterion of Section 7, over the flag
(half-edge) model of multigraph fragments. Numbered results are the
paper's — including Theorem 4.7, Corollary 4.10, Theorems 7.3 and 7.5
and Corollary A.2 — except those attributed to Regts and
Sevenster (RS21 below), whose Definition 5, Proposition 3,
Theorem 6, Lemma 11 and displayed equations are cited by their own
numbers, in the journal version's numbering. (The arXiv copy
numbers the displays (11)–(16) as (19)–(24), and numbers the
closing display of Theorem 6's proof, unnumbered in the journal,
as (25)–(26); the named results agree.)
The paper restates RS21's Definition 5 as Definition 2.1.

Claude Fable 5, Claude Opus 5, and GPT-6 Astra were used extensively
in developing this formalization; [formalization.yaml](formalization.yaml)
reports how. The paper this tree formalizes was developed with
Claude Fable 5, GPT-5.6 Sol Pro and GPT-6 Astra. Sol Pro contributed
to the paper only: it had no part in the Lean development, which is
the three models named in `formalization.yaml`.

## The theorems

`RS/Summit.lean` proves the Main Theorem and its sharp quantitative
form with no unproved mathematical input:

    theorem regts_sevenster : RegtsSevensterStatement

    theorem regts_sevenster_total : RegtsSevensterStatementTotal

    theorem regts_sevenster_characterisation
        (f : ClosedFragment → ℂ)
        (hempty : f emptyClosedFragment = 1)
        (hiso : ∀ W₁ W₂, W₁.Equiv W₂ → f W₁ = f W₂) :
        (∃ R : ℕ, EdgeRankBounded f R) ↔ IsMixedPartitionFunction f

Each depends on `propext`, `Classical.choice` and `Quot.sound` and
nothing else; the checks are pinned in
[`RS/Assembly/BlueprintDeligne.lean`](RS/Assembly/BlueprintDeligne.lean).

The certified `regts_sevenster_total` supplies a mixed model with
`k + 2ℓ ≤ R`, including at `R = 0`. Its witness has named fields for
the two dimensions, the vertex functional, the dimension inequality
and equality with the graph parameter. These definitions are pinned
by content in
[`RS/Assembly/BlueprintStatement.lean`](RS/Assembly/BlueprintStatement.lean)
and mirrored in the comparator challenge. This is the paper's
Main Theorem and Corollary 4.10 for natural `R`.

The separate bound `k, 2ℓ ≤ ⌊2eR⌋` is also available as
`regts_sevenster_quant : RegtsSevensterStatementQuant`. Its square
specialization proof is auxiliary; the paper's colour bound and
Lean's total-dimension theorem use the commutant argument.

Writing `d = k + 2ℓ` and `r_n = rk M_{f,2n}`, the paper's
Lemma 4.9 gives `d^(2n) ≤ r_n binom(n + d² − 1, d² − 1)` for
`d,n ≥ 1`. It combines the sum of surviving block dimensions
(Lemma 4.8), Cauchy–Schwarz and a commutant bound. The commutant is
taken in the ordinary endomorphism algebra of the total vector
space, including parity-reversing maps. Its matrix entries are
determined, up to signs, by the counts of the `d²` possible letter
pairs; those counts sum to `n`, giving the binomial factor.
Lean uses individual block faithfulness and the coarser count
`(n + 1)^(d²)` to prove `d^(2n) ≤ r_n (n + 1)^(2d²)`.
Both polynomial estimates, together with `r_n ≤ R^(2n)`, force
`d ≤ R`; the zero-dimensional case is immediate.
The separate steps and their axiom checks are linked through
[`RS/TheoremTotal.lean`](RS/TheoremTotal.lean) and
[`RS/Assembly/BlueprintSchur.lean`](RS/Assembly/BlueprintSchur.lean).

The following Section 7 results are also theorems of record in
[`RS/Summit.lean`](RS/Summit.lean):

* `regts_sevenster_minimum` supplies a model attaining
  `minimumColourDimension f.val`; `dimension_eq_minimum` proves
  its total dimension equals that minimum (Theorem 7.3(c)).
* `regts_sevenster_rank_growth` proves that
  `(connectionRank f.val (2n))^(1/(2n))` tends to the minimum
  colour dimension. The polynomial lower estimate and the converse
  upper bound give the limit, including when the minimum is zero
  (Lemma 7.1 and Theorem 7.3(a)).
* `regts_sevenster_prescribed` characterizes models on exactly
  `ℂ^{k|2ℓ}` by `PrescribedColourBounds`: rank base `k + 2ℓ` and
  free-circle value `k − 2ℓ`. The criterion includes `k = ℓ = 0`
  (Theorem 7.5).

[`RS/TheoremDimension.lean`](RS/TheoremDimension.lean) proves growth
and minimality. [`RS/TheoremPadding.lean`](RS/TheoremPadding.lean)
proves the prescribed-dimension criterion and the formulas recovering
both parity dimensions of a minimal model from the minimum and the
free-circle value (Theorem 7.3(b)). Its padding construction
(Lemma 7.2),
`MixedFunctional.padColours`, preserves the symplectic partners and
extends the functional by zero. The graph evaluation proof is in
[`RS/Novel/Skein/ColourPadding.lean`](RS/Novel/Skein/ColourPadding.lean).
These results have pinned statement and axiom audits in the
ordinary build; the comparator challenge retains its seven certified
statements.

Deligne's theorem on tensor categories, on which the forward
direction rests, is proved here rather than cited, in the
fibre-functor form that is the substance of his own proof
(`RS/Classical/Deligne/DeligneAssembly.lean`):

    theorem deligne_theorem : DeligneTheoremStatement

The converse — every mixed partition function has exponentially
bounded connection rank, base `max 1 (k + 2ℓ)` — does not depend on
it (`RS/TheoremConverse.lean`):

    theorem regts_sevenster_converse : RegtsSevensterConverseStatement

The forms carrying `DeligneTheoremStatement` as a hypothesis are
kept — `regts_sevenster_deligne_only`,
`regts_sevenster_quant_deligne_only`,
`regts_sevenster_total_deligne_only`, `regts_sevenster_iff` — since
they exhibit the dependency structure and are what a reader checking
the argument against the literature will want.

## The definitions

The main statement surface is
[`RS/Definitions.lean`](RS/Definitions.lean), whose only import is
the tree's Mathlib funnel (`RS/Common/MathlibDeps.lean`, an import
list with no content). The corollary surface is
[`RS/DimensionDefinitions.lean`](RS/DimensionDefinitions.lean),
which imports only `RS/Definitions.lean`. It defines the natural
connection rank, representation predicate, minimum total colour
bound and prescribed parity conditions. Reading these two files
against Mathlib determines the meaning of every summit.

It defines the flag model of multigraph fragments with its gluing,
isomorphism and composition; the edge-rank hypothesis class
(`EdgeRankParameter` — normalized at the empty graph,
isomorphism-invariant, connection pairings of rank at most `R ^ t`
at every arity); the paper's Definition 2.1 (RS21's Definition 5)
on the flag model
(`IsMixedPartitionFunction` — the sum over Eulerian edge subsets of
circuit-signed colouring sums against a `(k, 2ℓ)` vertex
functional, with the `(k − 2ℓ)^{circles}` free-circle convention);
the named statements, of which the first is

    RegtsSevensterStatement : Prop :=
      ∀ (R : ℕ) (f : EdgeRankParameter R), IsMixedPartitionFunction f.val

the sharp total-budget form `RegtsSevensterStatementTotal`
(Corollary 4.10), the auxiliary separate-budget form
`RegtsSevensterStatementQuant`, and the converse; the category of
super vector spaces; and `DeligneTheoremStatement`.

## What the theorems rest on

**Nothing is assumed.** The development rests on `propext`,
`Classical.choice` and `Quot.sound`, and on no cited mathematical
input. In particular:

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

  The statement is weaker than what Deligne proves, in two ways:
  it is one direction of his equivalence, and it takes the
  conclusion in fibre-functor form — an exact faithful
  ℂ-linear symmetric monoidal functor to finite-dimensional super
  vector spaces (`DeligneFibreFunctor`), which a ⊗-equivalence with
  the representations of an affine supergroup scheme yields by
  composing with the forgetful functor. The development consumes
  less again: the existence, sharp bound, growth and padding proofs
  use the symmetric monoidal ℂ-linear functor as `DelignePackage`,
  and `DeligneFibreFunctor.toPackage` forgets faithfulness and
  exactness. As in the paper's Lemma 7.1, the rank upper bound for
  growth comes from the converse theorem. The paper uses
  faithfulness separately in its survival-hook lemma (Lemma 7.6).

  `RS.deligne_theorem` proves that statement, the fibre-functor
  theorem used in the paper's Theorem 4.7
  (`RS/Classical/Deligne/DeligneAssembly.lean`). The route is not
  Deligne's own. His §4 descends the fibre functor along a
  faithfully flat `Isom⊗` torsor, which needs fppf descent of finite
  presentation, EGA IV₃ 11.2.6.1, descent along transitive
  groupoids, and the tensor product of abelian categories. Here the
  ⊗-generator alone is split, and one passes to a quotient by a
  maximal ideal: over a simple algebra the regular module and its
  twist by the odd line are simple objects of the module category,
  so a free mixed module is semisimple of finite length, and the
  objects that the algebra splits are closed under subquotients as
  well as sums, tensor products and duals. Finite ⊗-generation then
  reaches every object, the section data of Deligne's 2.10 comes
  free from semisimplicity, and the scalars are a field of countable
  dimension over ℂ, hence ℂ. This is the pattern of Coulembier,
  *Tannakian categories in positive characteristic*, Duke Math. J.
  **169** (2020), Lemma 3.3.2(ii), with Lemmas 1.2.10 and 1.5.2.

All of Deligne's hypotheses are discharged in the development for
the concretely constructed envelope
`Env f = Karoubi (Mat_ (Karoubi (SkeinObj f)))`
(`RS/Novel/Envelope/EnvDelignePackage.lean`), and the resulting
fibre functor is restricted along the braided linear embedding
back to the skein category.

The other classical inputs are theorems of the tree too:

* the classical symmetric-group input (`SchurPackage`) is a
  theorem (`RS.schurPackage`,
  `RS/Classical/SchurTheory/Package.lean`): the Jacobi–Trudi
  character theory — Frobenius formula, orthonormality,
  irreducible realization with sign, block theory, branching, and
  square-dimension growth — constructed from Mathlib's linear
  algebra;
* Regts–Sevenster's Proposition 3 is a theorem in both sectors,
  closed (`eulerianIndependence`) and open (`pairedLedger`);
* the paper's exponential-growth trace-zeta corollary (Corollary
  A.2) is formalized with its hypothesis and threshold — a real
  dimension bound `A`, *every*
  integer side `s > 2e√A`, and degrees at most `s − 1`. The
  appendix starts from a rigid symmetric ℂ-linear category with
  `End 𝟙 = ℂ` and an object `Z`, and derives the symmetric-group
  action on `Z ^ ⊗ n`, the propagation of vanishing, the traces and
  the Frobenius identity; that derivation is `objectFrobeniusTower`,
  so `traceZeta_rational_of_object` and its reduced super-spectrum
  form hold
  for an arbitrary category-and-object pair
  (`RS/Novel/Envelope/ObjectTower.lean`). The same conclusions over
  the derived interface alone are
  `FrobeniusTower.traceZeta_rational_sharp`
  (`RS/Novel/Envelope/TraceZetaSharp.lean`), which the skein
  endomorphism algebras instantiate directly. The appendix also
  gives a nilpotent-trace proof
  (`RS/Novel/Envelope/NilpotentTrace.lean`). The main chain uses
  the factorial argument below. The sequence lemmas
  `newtonH_series_rational_of_hook_vanishing` and
  `superPowerSums_of_hook_vanishing` formalize Lemma A.9 for
  arbitrary `a,b`, with numerator degree at most `b` and
  denominator degree at most `a`. The square case
  `a = b = s − 1` supplies Corollary A.2.

Schrijver's factorial-rank argument (arXiv:1211.3561, Proposition 4)
supplies the nilpotent-trace proof in the paper's Theorem 4.3 and
in Lean's mainline. Its common interface
`CycleTraceTower` contains only permutation representations,
tensor-power maps and the cycle-trace formula. A nonzero nilpotent
trace forces `n! ≤ finrank ℂ (E n)` at every finite-dimensional
level; a single level with smaller dimension suffices to rule it out.
Exponential growth is a corollary
([`FactorialTrace.lean`](RS/Classical/Algebra/FactorialTrace.lean)).
The categorical instance is
[`Envelope/FactorialTrace.lean`](RS/Novel/Envelope/FactorialTrace.lean);
the strand instance and its semisimplicity consequence are
[`BlockFactorialTrace.lean`](RS/Novel/Envelope/BlockFactorialTrace.lean).
`karoubiEnd_isSemisimpleRing_factorial` extends the same proof to
Karoubi corners. These lemmas have no Schur-package input, and their
transitive proof dependencies are checked in
[`BlueprintFactorial.lean`](RS/Assembly/BlueprintFactorial.lean).
The summit proofs use this route through matrix-envelope traces,
semisimplicity and abelianness. The audit checks that every forward
summit reaches the factorial trace theorem and has no dependency on
the appendix nilpotent-trace or trace-zeta mechanisms. The appendix
rationality theorems remain separately available.

This separation concerns the nilpotent-trace mechanism. The sharp
dimension bound uses block faithfulness: Lemma 4.8 bounds the sum
of surviving block dimensions; Lean uses the individual-block
bound stated in Lemma A.4. Deligne's internal proof also uses
symmetric-group theory.

The dependency-exhibiting form takes Deligne's theorem alone:

    theorem regts_sevenster_deligne_only
        (hDeligne : DeligneTheoremStatement.{1, 1}) :
        RegtsSevensterStatement

## Correspondence with the paper

Nine things differ from the paper's presentation, each deliberately:

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
* **The rank base is natural in Lean and real in the paper.**
  Hypothesis (H2) and the Main Theorem allow real `R ≥ 1`.
  `EdgeRankBounded` and `regts_sevenster_total` use `R : ℕ`,
  including zero. The existential characterization is unchanged:
  round a real base up, and use monotonicity
  (`EdgeRankBounded.mono`). Section 7.6 also recovers the sharp
  real budget from the formal results: take `B = ⌈R⌉`, construct
  a model with total dimension at most `B`, and use the certified
  even rank-growth limit to identify its dimension with a limit
  bounded by `R`. Theorem 7.5 and Lean both include zero colours.
* **The dimension estimate is proved by block faithfulness.** For
  `d = k + 2ℓ` and `d, n ≥ 1`, Lemma 4.9 bounds `d ^ (2n)` by
  `rk M_{f,2n}` times `binom (n + d² − 1) (d² − 1)`, using the sum of
  surviving block dimensions (Lemma 4.8) and Cauchy–Schwarz; the tree
  uses individual block faithfulness (Lemma A.4) to bound it by
  `rk M_{f,2n}` times `(n + 1) ^ (2 d²)`. Both count simultaneous
  word-pair orbits to bound the commutant in the ordinary
  endomorphism algebra of the total space, parity-reversing maps
  included, and both give `d ≤ R` and the same rank-growth limit.
* **The intrinsic dimension is defined as a minimum.**
  `minimumColourDimension` is the least total colour bound, and the
  even rank roots are proved to tend to it. The paper defines the
  growth base as the supremum of the rank roots over all positive
  arities and identifies it with that same minimum (Lemma 7.1 and
  Theorem 7.3).
* **The vertex functional is presented in sorted colour order.**
  `MixedFunctional` assigns values to multisets of even colours
  and *sets* of odd colours, with antisymmetry supplied by the
  sorting-sign evaluator (`evalOdd`). This evaluates the paper's
  κ-paired wedge in the sorted basis. The witness `hRS` is the
  paper's `h^ξ`, the raw star coefficient. Lemmas 5.6 and 5.7
  relate it to the mate-based functional by
  `h^RS = h^ξ ∘ Sym_s(Ψ)`, where `Ψ` fixes the even basis and
  sends `ξ_i` to `η_i`. This isometry preserves the twisted edge
  tensor and hence the partition function. Lean proves the
  graph-evaluation equality directly from star coordinates,
  partner signs and sorting signs.
* **Composition is written applicatively.** `Fragment.compose F G`
  glues the last `t` labels of `F` to the first `t` of `G`; it is
  the paper's `G ∘ F` and Mathlib's diagrammatic `F ≫ G`.
* **The appendix's growth constant is unconstrained in Lean.**
  Corollary A.2 fixes a real `A ≥ 1` in its growth hypothesis;
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
* **The super symmetric power is reached on coordinates.** The
  paper factors the functional `β_d(T_d, −)` through `Sym_s^d V`
  by combining the invariance of the pairing under the super
  `S_d`-action (its Lemma 5.1(b)) with the invariance of the star
  tensor. The tree works on coordinates instead: the star class
  absorbs any relabelling of its legs (`vertexStarClass_perm`),
  because all legs of a star meet the one vertex, and the model
  permutation acts on coordinates by the odd-inversion sign
  (`coordOf_modelPermMap'`). The two combine into `starCoord_perm`,
  which over `ℂ` is already the statement that the coordinate
  functional lives on `Sym_s^d V` — symmetric in the even letters,
  alternating in the odd ones. Lemma 5.1(b) is proved
  (`betaColour_perm'`) but is not consumed; 5.1(a) is.

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

The audit surface is small. What the theorems *mean* is
[`RS/Definitions.lean`](RS/Definitions.lean), self-contained over
Mathlib as above; what they *say* is the theorems-of-record files —
`RS/Summit.lean`, which carries the hypothesis-free forms, over
`RS/TheoremForward.lean`, `RS/TheoremQuant.lean`,
`RS/TheoremTotal.lean`, `RS/TheoremDimension.lean`,
`RS/TheoremPadding.lean` and `RS/TheoremConverse.lean`.
(`RS/Glossary.lean` glosses the vocabulary, and
`ClassicalOverview.md` surveys the classical layer.)

The `RS/Assembly/` audits then pin that surface.
`BlueprintStatement.lean` pins the type of every definition the
summits are phrased in and of every theorem of record with
`#guard_msgs`-guarded `#check` lines; `Blueprint.lean` and its
companion audits pin every main theorem's axiom set to
`[propext, Classical.choice, Quot.sound]` with guarded
`#print axioms` lines. Drift in either is a compile error, and both
audits are part of the default `lake build`.
`BlueprintFactorial.lean` also pins the factorial interface and
theorem statements and traverses their types and proof bodies to
exclude the Schur, hook-confinement, trace-zeta and Deligne engines.
The traversal includes opaque proofs and checks known dependencies
of the appendix proof as a control. It also checks that the summits
use the factorial theorem and exclude the appendix's nilpotent-trace
and trace-zeta mechanisms; Deligne and the colour bounds retain their
own symmetric-group arguments.

Two pins go beyond types. `mixedPartition` carries conventions a
type cannot see — the circuit sign, the Eulerian condition, a
loop's two incidences, the loop/free-circle distinction, the
`η`-convention — so it is also pinned by *value*: the paper's
worked example must evaluate to `θ − 2` on the loop graph and to
`0` with a free circle adjoined, and
`RS/Novel/Skein/LoopExample.lean` proves that it does. And
`DeligneTheoremStatement` is pinned by *content*: unfolded, with the
definition of every predicate its hypothesis list is phrased in, for
comparison against Deligne's Théorème 0.6 and §0.1.

## Certification

Beyond the in-tree audits, seven main declarations are certified
with [comparator](https://github.com/leanprover/comparator).
`Challenge.lean` is self-contained — it imports Mathlib and nothing
else, carries the statement surface itself, and states them with
`sorry`; `Solution.lean` proves each by the theorem of record of the
same name, against the identical definitions of
`RS/Definitions.lean`;
`comparator-config.json` lists the names and the axiom
whitelist. Comparator builds the two modules separately, exports
both environments at the kernel level — independently of the
elaborator — and checks that each theorem is proved with an
identical statement about identical definitions, that the proofs
use no axiom outside the whitelist, and that the kernel replays
them. The CI workflow (`.github/workflows/ci.yml`) runs the build,
the audits, the environment linters and the certification on every
push.

## Building

The tree pins Lean `v4.31.0` and Mathlib at its `v4.31.0` release
tag, so it builds from a clean clone:

    lake exe cache get      # Mathlib's prebuilt oleans
    lake build              # green, zero warnings

Budget around 11 GB of disk: roughly 8.5 GB for Mathlib and its
dependencies, source and oleans, and 2 GB for this tree's own build
products. Once the cache is in place, a clean build of the tree
takes about nine minutes on 128 hardware
threads; the wall time is dominated by the longest import chain, so
expect appreciably more on a small machine. Verifying the audits and
the summits:

    lake env lean RS/Assembly/BlueprintStatement.lean
    lake env lean RS/Assembly/Blueprint.lean
    lake env lean RS/Assembly/BlueprintConverse.lean
    lake env lean RS/Assembly/BlueprintSchur.lean
    lake env lean RS/Assembly/BlueprintDeligne.lean
    lake env lean RS/Assembly/BlueprintFactorial.lean

Each is silent on success. The tree carries no `sorry`, no custom
`axiom`, and no `native_decide`, and

    lake exe runLinter RS

reports `Linting passed for RS` — the Batteries linter suite, run
over every declaration in the tree, at zero findings.

    python3 scripts/check_style.py

checks the 80-column limit and the ban on typeclass `variable`
binders. The source checks and environment linters both run in CI.

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
[CC BY 4.0](https://creativecommons.org/licenses/by/4.0/).
