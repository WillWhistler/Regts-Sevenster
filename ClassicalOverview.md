# The classical layer: an overview

This document surveys the classical mathematics formalized in this
tree — the theorems of the literature that the Regts–Sevenster
development proves or consumes, the proof methods used, and where
those methods come from.  Several of the proofs below are
arrangements developed for this formalization rather than
transcriptions from the literature, and are described as such.
Every implication surveyed is kernel-checked from (a subset of) the
three standard axioms `[propext, Classical.choice, Quot.sound]`,
with no `sorry`, no custom `axiom`, and no `native_decide` (see
[RS/Assembly/Blueprint.lean](RS/Assembly/Blueprint.lean) for the
audit — part of the default `lake build` target — and
[RS/Glossary.lean](RS/Glossary.lean) for the vocabulary used
below).

The paper's main route is also the route of the Lean summits:
connection ranks give nondegenerate trace pairings; Schrijver's
factorial obstruction kills nilpotent traces; finite-dimensional
algebra gives the semisimple abelian envelope; Deligne supplies a
super fibre functor; and the commutant estimate gives `k + 2ℓ ≤ R`.
The paper develops growth, minimum dimension and padding in
Section 7. Its Appendix A gives an independent trace-zeta route.
Numbered references here follow the accompanying paper unless
attributed to another source. RS21's Definition 5 is the paper's
Definition 2.1.

No cited theorem is an unproved input. `DeligneTheoremStatement`
([RS/Definitions.lean](RS/Definitions.lean)) — Deligne's theorem on
tensor categories (Deligne 2002, Théorème 0.6 with §0.1; Ostrik,
Thm 2.3) — is proved in the tree as `RS.deligne_theorem`
([RS/Classical/Deligne/DeligneAssembly.lean](RS/Classical/Deligne/DeligneAssembly.lean)).

It carries Deligne's own hypotheses: essentially small, abelian,
ℂ-linear and rigid symmetric with ℂ-bilinear tensor product,
`End 𝟙 = ℂ`, finitely ⊗-generated, and of moderate growth in the
length of the tensor powers.  Its conclusion is taken in
fibre-functor form rather than as the ⊗-equivalence with the
representations of an affine supergroup scheme, which yields the
functor by composing with the forgetful functor; the development
then consumes the symmetric monoidal ℂ-linear functor as
`DelignePackage` for reconstruction, the sharp bound and the
formalized rank-growth and padding results. Their rank upper bound
comes from the converse theorem. The paper uses faithfulness in
its additional survival-hook criterion, Lemma 7.6.

The route is not Deligne's own.  His §4 descends the fibre functor
along a faithfully flat `Isom⊗` torsor, which calls on fppf descent
of finite presentation, EGA IV₃ 11.2.6.1, descent along transitive
groupoids, and the tensor product of abelian categories.  Here the
⊗-generator alone is split and one passes to a quotient by a maximal
ideal: over a simple algebra the regular module and its twist by the
odd line are simple objects of the module category, so a free mixed
module is semisimple of finite length, and the objects the algebra
splits are closed under subquotients as well as sums, tensor
products and duals.  Finite ⊗-generation then reaches every object,
the section data of Deligne's 2.10 comes free from semisimplicity,
and the scalars are a field of countable dimension over ℂ, hence ℂ.
This is the pattern of Coulembier's Lemma 3.3.2(ii), with his
Lemmas 1.2.10 and 1.5.2 (see the references).

Each step between what the theorem provides and what is used is also
proved: forgetting exactness and faithfulness, and reading the
growth hypothesis by composition length where the envelope's rank
bound gives endomorphism dimension.  The hypotheses themselves are
discharged for the concrete envelope (§5 below).

Everything else below is a theorem of the tree.


## 1. The flag model and the skein category

**Statement.**  Graph parameters live on *fragments*: multigraphs
presented by flags (half-edges) with a boundary of labelled
dangling legs, up to isomorphism (`Fragment`, `Fragment.Equiv`),
with a gluing calculus (`glueInterface`, `pairClose`) composing
fragments along ordered interfaces.  Hom spaces of the skein
category are spans of fragments modulo the parameter's pairing
kernel; the result is a ℂ-linear preadditive symmetric monoidal
category with exact self-duality at every arity (`skeinRigid`).

**Method and provenance.**  Connection matrices and their ranks
are the Freedman–Lovász–Schrijver framework (2007); diagram
categories whose Homs are graphs-with-boundary are the standard
skein/partition-category tradition (Brauer 1937 onward, Deligne's
interpolation categories).  The flag presentation with a linearly
ordered label alphabet — every relabeling in the development is
order-preserving, which is load-bearing for the open-sector signs
of §8 below — is an arrangement of this formalization.

The rank of a connection matrix is a rank of an infinite matrix,
and the literature reads it as the supremum of the ranks of the
finite submatrices.  The hypothesis class here bounds instead the
dimension of the row span, which needs no supremum; the two are the
same condition, and the general statement — a row span has
dimension at most `n` exactly when every finite submatrix has rank
at most `n` — is proved in
[RowSpanRank.lean](RS/Common/RowSpanRank.lean) and specialized in
[ConnectionRank.lean](RS/Novel/Skein/ConnectionRank.lean).  The one
point of substance is that a finite-dimensional space of functions
is separated by finitely many coordinates, which is what makes the
row rank visible on a single finite submatrix.

**Files.**  The flag model, gluing and composition are defined in
[RS/Definitions.lean](RS/Definitions.lean); the skein category is
built on them in `RS/Novel/Skein/`:
[HomSpaces.lean](RS/Novel/Skein/HomSpaces.lean), the monoidal stack
([MonoidalInstance.lean](RS/Novel/Skein/MonoidalInstance.lean),
[BraidedInstance.lean](RS/Novel/Skein/BraidedInstance.lean)), rigidity
([ExactPairingInstance.lean](RS/Novel/Skein/ExactPairingInstance.lean)).


## 2. Symmetric-group character theory (the Schur package)

**Statement.**  The classical representation theory of the
symmetric groups, assembled as `RS.schurPackage`
([RS/Classical/SchurTheory/Package.lean](RS/Classical/SchurTheory/Package.lean)): the
Jacobi–Trudi virtual characters are genuine irreducible characters
(sign included), the Frobenius character formula, orthonormality,
the central-idempotent block theory (block dimension `d²`, block
faithfulness), branching containment, and square-shape dimension
growth.

**Method and provenance.**  The results are Frobenius (1900),
Jacobi–Trudi, and Schur.  The proofs avoid the standard
combinatorial machinery entirely — no semistandard tableaux, no
RSK, no Littlewood–Richardson, no branching rule as input:

* orthonormality comes from the bialternant identity
  `s_μ·a_δ = a_{μ+δ}`, proved by a single-variable resolvent
  giving an entrywise matrix factorization of the alternant matrix
  ([Bialternant.lean](RS/Classical/SymFun/Bialternant.lean));
* branching positivity needs only the `p₁`-Pieri rule for
  alternants, a two-line signed-monomial reindexing (colliding
  exponents vanish as repeated rows) iterated along any
  single-box chain
  ([AlternantPieri.lean](RS/Classical/SymFun/AlternantPieri.lean),
  [PairingPos.lean](RS/Classical/SchurTheory/PairingPos.lean));
* the sign of the irreducible realization is resolved by
  evaluating the dimension determinant as a positive Vandermonde
  product of staircase differences — no hook lengths, no sign
  tracking ([SignResolve.lean](RS/Classical/SchurTheory/SignResolve.lean),
  [DescVandermonde.lean](RS/Classical/SymFun/DescVandermonde.lean)).

These arrangements were developed for this formalization; each is
self-contained at the alternant level, so the package as a whole
carries no combinatorial citations.  A smaller device in the same
spirit: extending the Jacobi–Trudi Leibniz sum to zero-padded
shapes needs no cancellation argument — in any guard-satisfying
term the permutation necessarily fixes every padded row, so the
padded sum restricts bijectively to the unpadded one
([JTPad.lean](RS/Classical/SchurTheory/JTPad.lean)).

**Files.**  `RS/Classical/SchurTheory/` (the character theory and blocks),
`RS/Classical/SymFun/` (the alternant calculus).


## 3. The trace-zeta results and the factorial trace argument

**Statement.** The exponential-growth form of the appendix,
Corollary A.2: for an object `X` of a
rigid symmetric ℂ-linear category with `End 𝟙 = ℂ` whose tensor
powers have finite-dimensional endomorphism algebras satisfying
`finrank (End (X ^ ⊗ n)) ≤ A ^ n`, with `A` an arbitrary
real, and for *every* integer `s > 2e√A`, the
trace zeta function of every endomorphism of `X` is `P/Q` with `P`
and `Q` coprime, of constant term `1` and of degree at most `s − 1`
(`traceZeta_rational_of_object`); equivalently the power traces are
a difference of power sums of two disjoint multisets of nonzero
complex numbers of sizes at most `s − 1`, the reduced super-spectrum
(`traceZeta_superSpectrum_of_object`).  The same conclusions over
the derived interface alone — a family of algebras carrying the
symmetric-group action, the traces and the Frobenius identity — are
`FrobeniusTower.traceZeta_rational_sharp` and
`traceZeta_superSpectrum_sharp`.  The threshold rests on sharp
square death (`square_growth_sharp`) through sharp hook confinement
(`PermTower.hook_confinement_sharp`), and the identification of the
zeta function with the complete-homogeneous series is
`traceZeta_eq_newtonH_series`.

The paper's Theorem A.1 starts from the death of one rectangle
`((b + 1)^(a + 1))` and gives numerator degree at most `b` and
denominator degree at most `a`. Its sequence lemma (Lemma A.9)
is formalized for arbitrary `a,b` in
`newtonH_series_rational_of_hook_vanishing` and
`superPowerSums_of_hook_vanishing`. Integer row shifts in the
Jacobi–Trudi recurrence and zero coefficients at negative degrees
retain both degree bounds when `a > b`. Corollary A.2 uses the
square case `a = b = s − 1`.

The existentially-quantified side (`traceZeta_rational`,
`RS/Novel/Envelope/TraceZeta.lean`) holds over an arbitrary Schur
package. The sharp form is stated over the assembled package,
because the constant comes from the block dimensions there. The
forward proof uses the factorial nilpotent-trace argument below.

The interface is what the appendix's own starting data supplies:
from a category and an object, the symmetric-group action on
`Z ^ ⊗ n`, the propagation of vanishing, the traces and the
Frobenius identity are derived from the trace calculus, and that
derivation is `objectFrobeniusTower`.  The skein endomorphism
algebras carry the same structure directly, giving an instance of
the appendix's rationality and nilpotent-trace results.

The derivation runs as follows.  The action is built by a recursion
that chooses no word in the adjacent transpositions — the top factor
is bubbled to its destination — so functoriality follows from mere
generation of `S_n` by those transpositions
([SymPerm.lean](RS/Novel/Envelope/SymPerm.lean)).  Vanishing
propagates because extending a permutation by fixed slots tensors
its action with the identity, and whiskering is an algebra map
([SymPermCast.lean](RS/Novel/Envelope/SymPermCast.lean)).  The
Frobenius identity needs the trace of a permutation against a tensor
power.  That trace is a class function and is multiplicative over a
block sum of permutations, the block sum acting blockwise on the
reassociation `X ^ ⊗ (p + q) ≅ X ^ ⊗ p ⊗ X ^ ⊗ q`
([TensorPowSplit.lean](RS/Novel/Envelope/TensorPowSplit.lean)); on a
single cycle it is the trace of the corresponding power, proved by
descending one arity at a time through the partial trace, whose
value on a braiding is the identity
([PartialTrace.lean](RS/Classical/CatTheory/PartialTrace.lean),
[CycleTrace.lean](RS/Novel/Envelope/CycleTrace.lean)).  Every
permutation is conjugate to a block sum of rotations along its full
cycle type, so the trace is the product of the cycle traces over
that type ([PermTrace.lean](RS/Novel/Envelope/PermTrace.lean)) — and
that is exactly the sum the classical Frobenius character formula
evaluates.

The categorical calculus that derivation runs on is standard
mathematics that Mathlib does not carry, so it is proved here:
the categorical trace of an endomorphism in a rigid symmetric
category, its cyclicity and its multiplicativity over the tensor
product; the partial trace over one factor, its two-sided linearity
over the untraced factor, and its compatibility with the full trace;
and the Eckmann–Hilton commutativity of the scalars `End 𝟙`, without
which the product over an unordered cycle type does not typecheck
([Trace.lean](RS/Classical/CatTheory/Trace.lean),
[PartialTrace.lean](RS/Classical/CatTheory/PartialTrace.lean),
[UnitEnd.lean](RS/Classical/CatTheory/UnitEnd.lean)).  The same
layer carries the bounded-length notion (`LengthLE`, defined in
[RS/Definitions.lean](RS/Definitions.lean) with its API in
[Length.lean](RS/Classical/CatTheory/Length.lean)) and the bound of
length by the endomorphism dimension that §5 below needs
([LengthBound.lean](RS/Classical/CatTheory/LengthBound.lean)).

**Method and provenance.**  Newton's identities relating power
sums to complete homogeneous functions are classical; the
uniqueness-of-solution packaging (a power series with constant
term 1 is determined by its logarithmic derivative) is the entire
content of the identification of the zeta function with the
complete homogeneous generating function, and is stated once and
used at both of its consumers.  The factorial input
`n! ≥ (n/e)^n` behind the threshold is one term of the
exponential series — `e^n ≥ n^n/n!` — with no appeal to Stirling
([SquareGrowthSharp.lean](RS/Classical/SchurTheory/SquareGrowthSharp.lean));
the Schur package's own growth field needs only to beat some
exponential, and uses the crude integral bound `n^n ≤ 3^n · n!`
([FactorialBound.lean](RS/Common/FactorialBound.lean)).

Appendix A.5 relates the rationality statement to the determinantal
rationality theorem of Kimura, Kimura and Takahashi (2012,
Proposition 3.10), applied to objects with endomorphisms and then
to the trace map on their split Grothendieck ring. It attributes
the sequence argument to Mazza and Weibel (2013, Proposition 4.14
and Corollary 4.15). Lean follows the paper's direct Jacobi–Trudi
recurrence proof, retaining the rectangular degree bounds.

**Files.**  The theorem for an object in
[ObjectTower.lean](RS/Novel/Envelope/ObjectTower.lean) and over the
interface in
[TraceZetaSharp.lean](RS/Novel/Envelope/TraceZetaSharp.lean), both
over [TraceZeta.lean](RS/Novel/Envelope/TraceZeta.lean) and
[HookConfinementSharp.lean](RS/Novel/Envelope/HookConfinementSharp.lean);
the series layer in `RS/Classical/SymFun/`
([ZetaRational.lean](RS/Classical/SymFun/ZetaRational.lean),
[ZetaExp.lean](RS/Classical/SymFun/ZetaExp.lean),
[RationalityFromRecurrence.lean](RS/Classical/SymFun/RationalityFromRecurrence.lean)).

**The mainline nilpotent-trace proof (paper Theorem 4.3).**
Schrijver's argument (arXiv:1211.3561, Proposition 4) uses the
cycle-trace formula directly. If a nilpotent has nonzero trace,
choose its last positive power with nonzero trace, say `y`.
Then `tr(y^m) = 0` for `m ≥ 2`.
At level `n`, the functional `a ↦ tr(a · y^⊗n)` is zero on every
nonidentity permutation and takes the nonzero value `tr(y)^n` at
the identity. Its translates separate all permutation operators,
so `n! ≤ dim End(X^⊗n)`. One finite-dimensional level of dimension
less than `n!` therefore suffices for nilpotent-trace vanishing;
exponential growth supplies such a level.

This proof is formalized over the smaller `CycleTraceTower`
interface in
[FactorialTrace.lean](RS/Classical/Algebra/FactorialTrace.lean), with
categorical and strand instances in
[Envelope/FactorialTrace.lean](RS/Novel/Envelope/FactorialTrace.lean)
and [BlockFactorialTrace.lean](RS/Novel/Envelope/BlockFactorialTrace.lean).
The latter also proves strand semisimplicity; the corner trace
criterion gives `karoubiEnd_isSemisimpleRing_factorial` in
[KaroubiSemisimple.lean](RS/Novel/Envelope/KaroubiSemisimple.lean).
[BlueprintFactorial.lean](RS/Assembly/BlueprintFactorial.lean)
checks their statements, axioms and transitive independence from
the Schur, hook-confinement, trace-zeta and Deligne engines. The
summits use the factorial route through the matrix envelope and its
abelian structure. The audit checks that each forward summit reaches
the factorial trace theorem and avoids the appendix nilpotent-trace
and trace-zeta mechanisms. The rationality and degree bounds above
remain separate conclusions of the appendix mechanism.


## 4. The sharp dimension bound and model dimensions

**Statement.** The paper's Lemma 4.9 gives, for the total dimension
`d = k + 2ℓ` of the reconstructed model and
`r_n = rk M_{f,2n}`, with `d,n ≥ 1`,

    d^(2n) ≤ r_n binom(n + d² − 1, d² − 1).

Together with `r_n ≤ R^(2n)`, this proves `d ≤ R`
(Corollary 4.10 and the quantitative clause of Theorem 1.1).
Lean's certified theorem is `RS.regts_sevenster_total`. It takes
`R : ℕ`, including zero; the paper states the sharp theorem for
real `R ≥ 1`.

**Method.** The super-permutation action on `V^⊗n` factors through
the skein algebra. Lemma 4.8 embeds the sum of the surviving simple
symmetric-group blocks in that algebra. If `m_λ` are the
multiplicities, Cauchy–Schwarz gives

    d^(2n) = (Σ_λ d_λ m_λ)²
        ≤ (Σ_{m_λ ≠ 0} d_λ²) (Σ_λ m_λ²)
        ≤ r_n dim End_{S_n}(V^⊗n).

The commutant is in the ordinary endomorphism algebra of the total
vector space, including parity-reversing maps. Conjugating matrix
units by super permutations permutes them up to signs. Simultaneous
permutation orbits of pairs of colour words are classified by the
counts of their `d²` possible letter pairs, giving commutant
dimension at most `binom(n + d² − 1, d² − 1)`, since the counts
sum to `n`.

Lean uses the individual-block bound of Lemma A.4 and counts
each letter-pair multiplicity independently between `0` and `n`:

    d^n = Σ_λ d_λ m_λ ≤ √r_n Σ_λ m_λ
        ≤ √r_n Σ_λ m_λ² = √r_n dim End_{S_n}(V^⊗n)
        ≤ √r_n (n + 1)^(d²).

Squaring gives its estimate `d^(2n) ≤ r_n (n + 1)^(2d²)`.
Either polynomial factor yields the sharp exponential base. The
block argument is independent of the appendix's trace-zeta and
nilpotent-trace mechanisms. Section 7.6 recovers the sharp real
budget from Lean's natural-base result and certified growth limit:
construct at `⌈R⌉`, then bound the dimension by the limit at `R`.

**Consequences.** The converse rank bound `r_n ≤ d^(2n)` squeezes
the even rank roots to `d`, including the zero-dimensional case
(Lemma 7.1). Applying that upper bound to any representing model
proves minimality (Theorem 7.3(c)). With `c = f(○) = k − 2ℓ`, a
minimal model has `k = (d + c)/2` and `ℓ = (d − c)/4`
(Theorem 7.3(b)).

The padding construction (Lemma 7.2) embeds symplectic pairs
together and extends the functional by zero. If prescribed
dimensions `K,2L` have the same free-circle value and bound the
ranks by `(K + 2L)^t`, the reconstructed dimensions satisfy
`k ≤ K` and `ℓ ≤ L`, so padding supplies exactly those dimensions
(Theorem 7.5). The criterion includes `K = L = 0`.

The formal declarations are `regts_sevenster_rank_growth`,
`regts_sevenster_minimum`, `regts_sevenster_prescribed`,
`TotalBoundedMixedModel.even_dimension_eq` and
`TotalBoundedMixedModel.half_odd_dimension_eq`.

**Files.** [TheoremTotal.lean](RS/TheoremTotal.lean),
[TheoremDimension.lean](RS/TheoremDimension.lean),
[TheoremPadding.lean](RS/TheoremPadding.lean),
[TotalDimension.lean](RS/Classical/Interfaces/TotalDimension.lean),
[WordCommutant.lean](RS/Classical/SchurTheory/WordCommutant.lean),
and [ColourPadding.lean](RS/Novel/Skein/ColourPadding.lean).

### Auxiliary square principal specializations

**Statement.**  Both nonvanishing statements behind the `⌊2eR⌋`
colour bound: `s_{(s^s)}(1^k) ≠ 0` for `k ≥ s`, and the negated
specialization via the identity
`s_{(s^s)}(1^{-m}) = (−1)^s · det[C(m, s+j−i)]` with the
right-hand determinant nonzero for `m ≥ s`. These prove the
separate-sector bound in `regts_sevenster_quant`. The paper's sharp
Corollary 4.10 uses the commutant argument above.

**Method and provenance.**  Classically these are cited through
the hook content formula.  Here both are citation-free: the
positive case by a complement symmetry that turns the
Jacobi–Trudi matrix into a polynomial family in the row
parameter, triangularized by Pascal column reduction into a ratio
of factorials times a manifestly positive Vandermonde product
([BinomialDet.lean](RS/Classical/SymFun/BinomialDet.lean)); the negated
case by a Lindström–Gessel–Viennot involution (Lindström 1973,
Gessel–Viennot 1985) on a path model of plain subset tuples — no
lattice-path geometry beyond prefix-count coordinates, and
positivity of the surviving count needs no enumeration, since the
constant families are non-crossing outright
([LGVStrict.lean](RS/Classical/SymFun/LGVStrict.lean)).

The square side's parity matters in this auxiliary argument: the
all-odd tensor block of the `n`-th super power lies in the even
part exactly when `n` is even, so the supertrace argument runs at
side `s` for even `s` but must run at side `s + 1` for odd `s` —
the displayed bound survives because `2ℓ` is even, so
`2ℓ < s + 1` still forces `2ℓ ≤ s − 1`. The square
specialization lemmas also carry an explicit positive-side guard.

**Files.**  Above, plus the assembly in
[RS/TheoremQuant.lean](RS/TheoremQuant.lean) and
[SquareGrowthSharp.lean](RS/Classical/SchurTheory/SquareGrowthSharp.lean).


## 5. The envelope and Deligne's hypotheses

**Statement.**  The double completion
`Env f = Karoubi (Mat_ (Karoubi (SkeinObj f)))` carries monoidal,
braided, symmetric, additive and ℂ-linear structure through all
layers; it is rigid, abelian, and semisimple; and it satisfies
Deligne's hypotheses — small, hence essentially so, `End 𝟙 = ℂ`,
finitely tensor-generated, and of moderate length growth
(`env_delignePackage`).  The growth hypothesis is the one that
needs translating: the envelope bounds the dimensions of the
endomorphism algebras of the tensor powers, and in a semisimple
category with finite-dimensional Hom-spaces that bounds their
composition lengths, which is what Deligne's theorem asks
(`moderateLengthGrowth_of_endGrowth`, over `LengthLE`).
Semisimplicity and finite-dimensional Hom-spaces are used for that
translation and for abelianness; neither is a hypothesis of the
theorem.  The generator is verified in a stronger form than the
theorem asks — every object a retract of a finite biproduct of pure
tensor powers of the strand, where a subquotient of a biproduct of
mixed powers would do (`env_strandRetract`,
`tensorGeneratedBy_of_retract`).  The
resulting fibre functor restricts along the braided linear
embedding back to the skein category (`skein_delignePackage`).

**Method and provenance.**  The framework is Deligne (2002) and
Ostrik.  Three proof arrangements are of this formalization:

* rigidity lifts through Karoubi by the mate-collapse
  observation — the dual of `(X, p)` is `(X^∨, p^∨)` with
  corrected cup and cap, and the first snake identity, after the
  idempotents are slid around, *is* the defining formula of the
  adjoint mate, so no string-diagram computation is needed
  ([KaroubiRigid.lean](RS/Novel/Envelope/KaroubiRigid.lean),
  [MatRigid.lean](RS/Novel/Envelope/MatRigid.lean));
* abelianness needs no abelian-envelope theory: inside
  finite-dimensional semisimple End algebras every morphism is
  von Neumann regular, so kernels and cokernels are literal
  idempotent splittings and normality of monos and epis follows
  from the same splittings
  ([EnvAbelian.lean](RS/Novel/Envelope/EnvAbelian.lean));
* semisimplicity follows from the factorial obstruction → nilpotent
  traces → semisimple End algebras
  ([BlockFactorialTrace.lean](RS/Novel/Envelope/BlockFactorialTrace.lean),
  [NilpotentMatTrace.lean](RS/Novel/Envelope/NilpotentMatTrace.lean),
  [EnvSemisimple.lean](RS/Novel/Envelope/EnvSemisimple.lean)).
  This chain and abelianness require no Schur package.
  Finite-dimensional Hom-spaces, `End 𝟙 = ℂ`, the tensor generator
  and the endomorphism-dimension bound also follow from the rank
  bound. All envelope hypotheses therefore precede the use of
  Deligne's theorem independently of the Schur and appendix engines.

**Files.**  `RS/Novel/Envelope/`; the block Frobenius tower at every
ambient arity ([BlockTower.lean](RS/Novel/Envelope/BlockTower.lean)).


## 6. Deligne's theorem

**Statement.**  `RS.deligne_theorem : DeligneTheoremStatement`: an
essentially small abelian ℂ-linear rigid symmetric monoidal category
with ℂ-bilinear tensor product, `End 𝟙 = ℂ`, a finite tensor
generator and moderate growth of the lengths of its tensor powers
admits an exact faithful ℂ-linear symmetric monoidal fibre functor
to finite-dimensional super vector spaces.

**Method and provenance.**  The statement quantifies over essentially
small categories, and `deligneTheoremStatement_of_small` reduces it
to a genuinely small one by transporting every structure across
`Monoidal.Transported (equivSmallModel A)`.  A tensor category need
not contain an odd line, so the small category is replaced by its
ℤ/2-graded doubling, whose ind-completion carries one, and the fibre
functor is restricted back along the even embedding at the end.

Over the doubling, §2's Schur layer supplies the growth dichotomy:
moderate length growth forces every object to be killed by a Schur
functor.  Deligne's §2 then produces, for a single object, an algebra
in the ind-completion over which that object becomes a mixed sum of
copies of the unit and of the odd line, and the countable descent
replaces it by a countably presented one.  Passing to the quotient by
a maximal ideal — Zorn over the ideals of an algebra object, whose
chain condition holds because the unit is a compact object of the
ind-completion — makes it simple.

Simplicity is what carries the splitting from one object to all of
them.  A simple algebra is a simple object of its own module
category, and so is its twist by the odd line, the odd line being
invertible; so a free mixed module is semisimple of finite length,
and every subobject, quotient and subquotient of one is again free
mixed.  The objects the algebra splits are therefore closed under
subquotients, and also under sums, tensor products and duals, so a
finite tensor generator drags the whole category into the class.
The locally split short exact sequences of Deligne's 2.10 come free
from the same semisimplicity: an epimorphism out of a semisimple
object splits.

The scalars are then read off.  The even part of the Γ-algebra of a
simple algebra is a field — multiplication by a nonzero scalar has
an ideal for its kernel and an ideal for its image, so simplicity
makes it invertible — and the odd part vanishes, an odd element
squaring to zero.  The algebra is a quotient of a countably presented
one, so that field has countable dimension over ℂ, hence is ℂ.  The
fibre functor therefore lands in super ℂ-vector spaces with no base
change to arrange, and (2.11.1)'s comparison map makes it symmetric
monoidal, exactness and faithfulness following from the freeness.

**Divergence from the source.**  Deligne's §4 obtains the passage
from an arbitrary nonzero algebra to ℂ by descent along a faithfully
flat `Isom⊗` torsor, which needs fppf descent of finite
presentation, EGA IV₃ 11.2.6.1, descent along transitive groupoids
and the tensor product of abelian categories.  None of that appears
here.  Two facts rule out the shortcuts one might try instead: the
category may have uncountably many isomorphism classes of objects
(`Rep(𝔾_a²)` satisfies every hypothesis, and pairs of commuting
nilpotent matrices have moduli), so an index family running over all
objects gives no dimension bound on the scalars; and finite tensor
generation is generation by *subquotients* only — for the Borel in
`SL₂`, the weight `+1` subobject of the standard representation is a
quotient of no sum of tensor powers, because the heads of those sums
carry only weights `≤ 0`.  Splitting one object and passing to a
simple quotient avoids both.  This is the pattern of Coulembier's
Lemma 3.3.2(ii), with his Lemmas 1.2.10 and 1.5.2.

Proposition 2.1 is also available in the form Deligne states it,
for a category whose ind-completion need not carry an odd line:
`RS.exists_fibre_functor_general`
([Prop21General.lean](RS/Classical/Deligne/Prop21General.lean))
produces the algebra of the doubling together with a fibre functor
that is strong monoidal, exact and faithful over it, before any
question of the scalars arises.

**Files.**  `RS/Classical/Deligne/`, behind the umbrella
[RS/Classical/Deligne.lean](RS/Classical/Deligne.lean); the assembly
in
[DeligneAssembly.lean](RS/Classical/Deligne/DeligneAssembly.lean).


## 7. Extraction and reconstruction

**Statement.**  From the restricted fibre functor: the standard
super model `stdSuper k ℓ`, the contraction identities the snake
relations supply (`exists_contraction_families`), the star
factorization of vertex functionals, and the reconstruction of
Definition 2.1's `mixedPartition` from the categorical scalar (the
paper's Theorem 6.1) — assembling `regts_sevenster` and, with
Section 4's dimension estimate, `regts_sevenster_total`.

**Method and provenance.**  The extraction follows the paper's
§5–§6, with the following differences of presentation.

The circuit-sign computation avoids circuit decompositions, the
consecutive-pairing choice, and the per-circuit `(−1)^{n−1}`
count entirely: the walk permutation preserves orientation
classes and is conjugated to its inverse by the direction swap,
so its orbits are two copies of its restriction to outgoing
half-edges and the circuit sign is
`(−1)^{#edges} · sign(walk|_{out})` — a permutation sign; the
regrouping parity against the vertex-pair word is then elementary
inversion counting.  Any transition system and orientation works,
so no admissibility discussion is needed.

The paper defines the mate-based functional by
`β_d(T_d, −) = h^cat_d ∘ varpi_d`, and then takes `h^RS = h^cat ∘ J`.
Lemma 5.6 identifies its value on a sorted monomial with the
coefficient of the star tensor in the corresponding word of the
`e_i, η_i` basis: `J` cancels the interleaving sign of `β_d`.
Lean defines `hRS` as `starCoord` at `canonColouring`, reading
coefficients in the `e_i, ξ_i` basis instead. This is the paper's
`h^ξ`. Lemma 5.7 gives the exact relation
`h^RS = h^ξ ∘ Sym_s(Ψ)`, where `Ψ(e_i) = e_i` and `Ψ(ξ_i) = η_i`.
The map `Ψ` is an even isometry preserving the copairing and its
parity twist, so the two functionals define the same partition
function. Lean's `evalOdd` supplies the sorting sign, and the
colouring evaluation supplies the symplectic partners; the endpoint
theorem `parameter_eq_mixedPartition` proves that the raw-coordinate
witness represents `f`. Both constructions use unscaled symmetric
and exterior monomials, with no factorial normalization.

The super symmetric power is reached on coordinates.  The paper
factors `β_d(T_d, −)` through `Sym_s^d V` from the invariance of
the pairing under the super `S_d`-action (its Lemma 5.1(b)) together
with the invariance of the star tensor.  The tree takes the
invariance one level earlier and geometrically: all legs of a vertex
star meet the one vertex, so the star class absorbs any relabelling
of them (`vertexStarClass_perm`), and the model permutation acts on
coordinates by the odd-inversion sign (`coordOf_modelPermMap'`).
Their combination `starCoord_perm` is already, over `ℂ`, the
statement that the coordinate functional lives on `Sym_s^d V`:
symmetric in the even letters, alternating in the odd ones.  No
quotient argument is interposed, and no property of the pairing is
needed.  Lemma 5.1(b) is proved (`betaColour_perm'`) but unused;
5.1(a) (`betaDiag_eq_betaColour`) is consumed.

**Files.**  `RS/Novel/Extraction/` (the standard super model, its
self-duality and the snake identities), `RS/Classical/Super/` (the
colouring model), and
`RS/Novel/Coordinates/` (the coordinate calculus and the sign
ledgers: [RegroupSign.lean](RS/Novel/Coordinates/RegroupSign.lean),
[PatternInv.lean](RS/Novel/Coordinates/PatternInv.lean),
[MasterSum.lean](RS/Novel/Coordinates/MasterSum.lean)); the theorem in
[RS/TheoremForward.lean](RS/TheoremForward.lean) and
[RS/TheoremTotal.lean](RS/TheoremTotal.lean).


## 8. Proposition 3, both sectors

**Statement.**  Regts–Sevenster's Proposition 3 (independence of
the Definition 5 summand from the transition system), proved
rather than cited — closed sector in full interface strength over
arbitrary ambient fragments (`eulerianIndependence`), and the
open sector in its corrected form: the chord-signed canonical
value of an open Eulerian subset is a function of its boundary
pairing alone (`pairedLedger`,
[RS/Novel/Skein/PropThreeOpen.lean](RS/Novel/Skein/PropThreeOpen.lean)).

**Method and provenance.**  The closed case has a short
normal-form proof — reindex the odd-colouring sum by the
partner-flip involution, after which the summand evaluates, for
every transition system and orientation, to one choice-free
expression — notable because the "obvious" transition-switch
connectivity argument has a genuine gap: two transition systems
need not admit a common compatible orientation (the overlay of
the two matchings with the edge involution can be non-bipartite),
so fixed-orientation switch chains do not connect all pairs.

Each convention in the open sector's package answers a way the
naive statement fails:

* the summand of an *open* subset depends on the orientation of
  its boundary-to-boundary chains — on the one-vertex four-leg
  fragment two path-canonical orientations give `−1` and `0`
  (`cSummand_O`, `lvSummand₂flip`); the per-edge sign ratio
  telescopes to `+1` only around closed circuits, so chains are
  oriented low-label-to-high, the unique convention compatible
  with the ordered cut factor;
* it depends on *which* boundary ends the system chains together:
  a two-chain re-pairing at a shared vertex transforms the summand
  by the constant factor `−1` (`twoPath_transform`), independent
  of the state and of the data at the four re-paired ends, and the
  corrected value carries a Pfaffian chord sign under which
  invariance is restored — crossing-type re-pairings flip both the
  summand and the chord sign, parallel-type flip neither;
* cross-pairing independence is refuted outright
  (`not_throughIndependenceC`: on that same fragment, the
  path-canonical values `−1` and `0` sit across two different
  boundary pairings) — the value is a function on boundary
  pairings, and the true statement is independence within each
  pairing fibre;
* single re-pairings do not connect a fibre: two chains crossing
  at two vertices give routings that share their pairing while
  every single re-pairing leaves it, so the move relation is the
  pairing-returning block `PairedStep` rather than the single step;
* a non-separated move has no state-preserving scalar transform
  law.  Its ledger (`twoPathNonSep_transform`) multiplies by the
  flipped chain's two end-colour symplectic signs *and* evaluates
  at a boundary state relabelled at exactly those two labels; the
  transported orientation around a pairing-returning loop
  correspondingly need not return.

The resulting structure — a local system over the pairing
groupoid acting simultaneously on pairings, orientation classes,
and boundary states, trivialized by one induction that carries
the canonical frame, the status-difference state identification,
and an explicit flip-sign product — was developed for this
formalization.  On closed fragments all of it is invisible, which
is why the literature never needed it.

**Files.**  The Prop-3 slice machinery of `RS/Novel/Skein/`
([PairedAssembly.lean](RS/Novel/Skein/PairedAssembly.lean) and its
supporting files), the closed sector in
[AllInternalAgreement.lean](RS/Novel/Skein/AllInternalAgreement.lean).


## 9. The converse machinery

**Statement.**  Every mixed partition function has exponentially
bounded connection rank — Regts–Sevenster's Theorem 6, which the
paper cites rather than reproves — with exact base `k + 2ℓ` in
`mixedPartition_edgeRankBounded`, including zero. The existential
statement `regts_sevenster_converse` uses `max 1 (k + 2ℓ)`. This
direction is a theorem of the development, resting on no input
(`regts_sevenster_converse`).  It
goes through one displayed identity, `SuperGramIdentity` — the
closure of two fragments, evaluated by the mixed partition function,
is the super form of their two fragment tensors — proved as
`superGramIdentity`.

**Method and provenance.**  The rank-bound frame (state
factorizations bound connection rank) is the classical
connection-matrix argument (Freedman–Lovász–Schrijver, Lovász).
The identity is Regts–Sevenster's own §4 argument, carried out over
the flag model: Lemma 11 on directed perfect matchings, the super
form (11), the normalised tensor and its invariance under reversing
a trail (12), the pairing identity (13), the sign composition (14)
and the vanishing across a mismatch (16).  The composition's side is
a colouring recursion over the interface, and the Eulerian position
RS21's step 1 asks for is supplied by the composition's own
orientation, which alternates across every interface pair.  A cut
that closes turns its edge into a free circle whose two branches
weigh `k` and `−2ℓ`, so a base subset's whole colour sum is the
composition's own term at its image times the free circles its own
closing cuts contribute; that product is choice-free at the closed
top, which is what lets the base sum be read one subset at a time.

**Files.**  The §4 route:
[RSTensor.lean](RS/Novel/Skein/RSTensor.lean),
[EdgeSum.lean](RS/Novel/Skein/EdgeSum.lean),
[ColourGlue.lean](RS/Novel/Skein/ColourGlue.lean),
[EdgeTerm.lean](RS/Novel/Skein/EdgeTerm.lean),
[ColourRecursion.lean](RS/Novel/Skein/ColourRecursion.lean),
[InterfaceAlternate.lean](RS/Novel/Skein/InterfaceAlternate.lean),
[ConverseAssembly.lean](RS/Novel/Skein/ConverseAssembly.lean),
[ConverseLift.lean](RS/Novel/Skein/ConverseLift.lean),
[ConverseTrip.lean](RS/Novel/Skein/ConverseTrip.lean),
[ConversePair.lean](RS/Novel/Skein/ConversePair.lean),
[ConverseFamily.lean](RS/Novel/Skein/ConverseFamily.lean), with the
identity in
[ConverseIdentity.lean](RS/Novel/Skein/ConverseIdentity.lean) and the
theorems in [TheoremConverse.lean](RS/TheoremConverse.lean).  The
per-cut engine underneath:
[GlueSplitProof/A.lean](RS/Novel/Skein/GlueSplitProof/A.lean),
[GlueSplitProof/C.lean](RS/Novel/Skein/GlueSplitProof/C.lean),
[CutSubsetSum.lean](RS/Novel/Skein/CutSubsetSum.lean),
[ThroughEdgeCut.lean](RS/Novel/Skein/ThroughEdgeCut.lean),
[ClosedCutDispatch.lean](RS/Novel/Skein/ClosedCutDispatch.lean).


## 10. Recurring techniques

A few mathematical devices appear throughout and are worth
knowing on sight:

* **Explicit sign ledgers.**  Signs are never tracked implicitly:
  each move carries a named ledger (flip-sign products, crossing
  deltas, four-label parities) and global statements are
  telescopes of per-step ledgers.  Where the literature says
  "signs cancel", the tree has an induction carrying the sign as
  data.

* **Fibrewise decomposition over boundary data.**  Open-sector
  statements decompose over induced boundary states or boundary
  pairings, with the closed statement as the one-fibre instance —
  the correct generalization in every case where the naive
  transport is false.  Where a statement is refuted, the
  refutation is a theorem of the tree
  ([ThroughIndCFalse.lean](RS/Novel/Skein/ThroughIndCFalse.lean),
  on the worked instance of
  [TransposeLedger.lean](RS/Novel/Skein/TransposeLedger.lean) and
  [LoopVerify.lean](RS/Novel/Skein/LoopVerify.lean)).

* **Order-preserving relabelings only.**  The label alphabet is
  linearly ordered and every relabeling in every composition
  chain is monotone; the odd-sector cut factor is antisymmetric
  under end swaps, so one non-monotone step would silently break
  the factorization.


## 11. Reading order

[RS/Definitions.lean](RS/Definitions.lean) defines the main
statements; [RS/DimensionDefinitions.lean](RS/DimensionDefinitions.lean)
defines the growth, minimum and prescribed-dimension vocabulary.
[RS/Glossary.lean](RS/Glossary.lean) glosses the vocabulary;
[README.md](README.md) states the theorems and their audit coverage.


## References

* G. Regts, B. Sevenster, *Mixed partition functions and
  exponentially bounded edge-connection rank*, Ann. Inst. Henri
  Poincaré D 8 (2021), 179–200; arXiv:1807.04494.
* P. Deligne, *Catégories tensorielles*, Mosc. Math. J. 2 (2002),
  227–248.
* V. Ostrik, *Tensor categories (after P. Deligne)*,
  arXiv:math/0401347.
* K. Coulembier, *Tannakian categories in positive characteristic*,
  Duke Math. J. 169 (2020), 3167–3219; arXiv:1812.02452.
* M. Freedman, L. Lovász, A. Schrijver, *Reflection positivity,
  rank connectivity, and homomorphism of graphs*, J. Amer. Math.
  Soc. 20 (2007), 37–51.
* A. Schrijver, *Characterizing partition functions of the
  edge-coloring model by rank growth*, J. Combin. Theory Ser. A
  136 (2015), 164–173; arXiv:1211.3561, Proposition 4.
* K. Kimura, S.-I. Kimura, N. Takahashi, *Motivic zeta functions
  in additive monoidal categories*, J. K-Theory 9 (2012), 459–473;
  [doi:10.1017/is011011006jkt174](https://doi.org/10.1017/is011011006jkt174).
* C. Mazza, C. Weibel, *Schur-finiteness in λ-rings*, J. Algebra
  374 (2013), 66–78; arXiv:1011.1444.
* F. G. Frobenius, *Über die Charaktere der symmetrischen Gruppe*,
  Sitzungsber. Preuss. Akad. Wiss. (1900), 516–534.
* B. Lindström, *On the vector representations of induced
  matroids*, Bull. London Math. Soc. 5 (1973), 85–90.
* I. Gessel, G. Viennot, *Binomial determinants, paths, and hook
  length formulae*, Adv. Math. 58 (1985), 300–321.
