import RS.Assembly.Blueprint
import RS.Novel.Envelope.ObjectTower

/-!
# Blueprint: the Schur package, the dimension bound, the open sector

The second part of the axiom audit.  It pins the symmetric-group
input the forward direction rests on, the sharp `⌊2eR⌋` dimension
bound, and the open-sector Proposition 3.  Read `Blueprint.lean`
first: it audits the forward proof itself.
-/

/-! ### The Schur package

Jacobi–Trudi characters: the Frobenius identity, orthonormality,
the branching containment, the block faithfulness and the square
growth bound — the fields of `SchurPackage`, and the package.
-/

/-- info: 'RS.jtChar_frobenius'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.jtChar_frobenius'

/-- info: 'RS.jtChar_orthonormal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.jtChar_orthonormal

/-- info: 'RS.jtChar_eq_nChar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.jtChar_eq_nChar

/-- info: 'RS.nProjector_block_faithful' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.nProjector_block_faithful

/-- info: 'RS.square_growth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.square_growth

/-- info: 'RS.branching_of_pairing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.branching_of_pairing

/-- info: 'RS.jtChar_pad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.jtChar_pad

/-- info: 'RS.schurPackageOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.schurPackageOf

/-- info: 'RS.restrPairing_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.restrPairing_ne_zero

/-- info: 'RS.schurPackage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.schurPackage

/-! ### The forward theorem on Deligne alone -/

/-- info: 'RS.regts_sevenster_deligne_only' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.regts_sevenster_deligne_only

/-! ### The trace zeta function

The zeta function of a Frobenius tower is the Newton generating
series of its super power sums, and rational when the characters
are hook-confined.
-/

/-- info: 'RS.FrobeniusTower.traceZeta_rational' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.FrobeniusTower.traceZeta_rational

/-- info: 'RS.FrobeniusTower.traceZeta_superSpectrum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.FrobeniusTower.traceZeta_superSpectrum

/-- info: 'RS.traceZeta_eq_newtonH_series' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.traceZeta_eq_newtonH_series

/-! ### Theorem A.1 with the sharp threshold

The appendix's own statement: a real dimension bound `A`, every side
`s > 2e√A`, and degrees at most `s − 1`.
-/

/-- info: 'RS.FrobeniusTower.traceZeta_rational_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.FrobeniusTower.traceZeta_rational_sharp

/-- info: 'RS.FrobeniusTower.traceZeta_superSpectrum_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.FrobeniusTower.traceZeta_superSpectrum_sharp

/-- info: 'RS.PermTower.hook_confinement_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.PermTower.hook_confinement_sharp

/-- info: 'RS.newtonH_series_rational_of_hook_vanishing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.newtonH_series_rational_of_hook_vanishing

/-! ### The sharp dimension bound

The `⌊2eR⌋` bound: a square diagram past it is dead, its
idempotent acts as zero, and the surviving sector is bounded.
-/

/-- info: 'RS.square_growth_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.square_growth_sharp

/-- info: 'RS.PermTower.not_alive_square_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.PermTower.not_alive_square_sharp

/-- info: 'RS.skeinRep_square_dead' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.skeinRep_square_dead

/-- info: 'RS.functional_charIdempotent_signed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.functional_charIdempotent_signed

/-- info: 'RS.charIdempotent_image_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.charIdempotent_image_ne_zero

/-- info: 'RS.EdgeSubset.RelTransitionSystem.pathMatch_invol' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.EdgeSubset.RelTransitionSystem.pathMatch_invol

/-- info: 'RS.superPermAction_square_dead' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.superPermAction_square_dead

/-- info: 'RS.mixedPartition_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.mixedPartition_empty

/-- info: 'RS.squareSectorBound_of_detPos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.squareSectorBound_of_detPos

/-- info: 'RS.diagramSchur_square_const_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.diagramSchur_square_const_ne_zero

/-- info: 'RS.regts_sevenster_quant_of_detPos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.regts_sevenster_quant_of_detPos

/-- info: 'RS.squareBinomialDetPos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.squareBinomialDetPos

/-- info: 'RS.det_binomial_upper_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.det_binomial_upper_ne_zero

/-- info: 'RS.regts_sevenster_quant_deligne_only' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.regts_sevenster_quant_deligne_only

/-! ### The open sector: Proposition 3

Repair connectivity of a pairing fibre, the canonical frame and
its re-canonicalization, the per-move ledgers and the paired step
— together, the signed value depends on the boundary pairing and
nothing else.  Independence *across* pairings is false.
-/

/-- info: 'RS.EdgeSubset.repair_connectivity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.EdgeSubset.repair_connectivity

/-- info: 'RS.eulerian_iff_parts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.eulerian_iff_parts

/-- info: 'RS.EdgeSubset.openCircuitCount_glueOpen_participating' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.EdgeSubset.openCircuitCount_glueOpen_participating

/-- info: 'RS.EdgeSubset.pathCanonical_agree_nonperiodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.EdgeSubset.pathCanonical_agree_nonperiodic

/-- info: 'RS.EdgeSubset.exists_pathCanonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.EdgeSubset.exists_pathCanonical

/-- info: 'RS.third_chord_reparity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.third_chord_reparity

/-- info: 'RS.EdgeSubset.pairingConnectivity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.EdgeSubset.pairingConnectivity

/-- info: 'RS.EdgeSubset.stepLedger_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.EdgeSubset.stepLedger_single

/-- info: 'RS.EdgeSubset.throughSummand_independence_of_allInternal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.EdgeSubset.throughSummand_independence_of_allInternal

/-- info: 'RS.EdgeSubset.twoPath_transform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.EdgeSubset.twoPath_transform

/-- info: 'RS.EdgeSubset.pathMatch_repair_swap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.EdgeSubset.pathMatch_repair_swap

/-- info: 'RS.crossesCut_iff_chordPairCross' depends on axioms: [propext] -/
#guard_msgs in
#print axioms RS.crossesCut_iff_chordPairCross

/-- info: 'RS.EdgeSubset.pathSign_of_samePairing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.EdgeSubset.pathSign_of_samePairing

/-- info: 'RS.EdgeSubset.signedValueAt_samePairing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.EdgeSubset.signedValueAt_samePairing

/-- info: 'RS.EdgeSubset.pairedLedger_iff_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.EdgeSubset.pairedLedger_iff_value

/-- info: 'RS.EdgeSubset.signedValueAt_samePairing_of_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.EdgeSubset.signedValueAt_samePairing_of_value

/-- info: 'RS.TransposeVerify.not_throughIndependenceC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.TransposeVerify.not_throughIndependenceC

/-- info: 'RS.cutPartner_eq_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.cutPartner_eq_some

/-- info: 'RS.eulerianIndependence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.eulerianIndependence

/-- info: 'RS.EdgeSubset.throughSummand_portFlip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.EdgeSubset.throughSummand_portFlip

/-- info: 'RS.EdgeSubset.twoPathNonSep_transform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.EdgeSubset.twoPathNonSep_transform

/-- info: 'RS.EdgeSubset.throughValueC_eq_signedValueAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.EdgeSubset.throughValueC_eq_signedValueAt

/-- info: 'RS.EdgeSubset.chainDir_pathMatch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.EdgeSubset.chainDir_pathMatch

/-- info: 'RS.EdgeSubset.pathCanonical_iff_chainDir' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.EdgeSubset.pathCanonical_iff_chainDir

/-- info: 'RS.EdgeSubset.exists_recanonicalize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.EdgeSubset.exists_recanonicalize

/-- info: 'RS.EdgeSubset.swap_dirs_opposite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.EdgeSubset.swap_dirs_opposite

/-- info: 'RS.EdgeSubset.mem_antiLowSet_transport_untouched' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.EdgeSubset.mem_antiLowSet_transport_untouched

/-- info: 'RS.EdgeSubset.chainDir_true_iff_high' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.EdgeSubset.chainDir_true_iff_high

/-- info: 'RS.EdgeSubset.mem_antiLowSet_transport_of_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.EdgeSubset.mem_antiLowSet_transport_of_canonical

/-- info: 'RS.EdgeSubset.pairedLedger_iff_unsigned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.EdgeSubset.pairedLedger_iff_unsigned

/-- info: 'RS.stateOddFlipSet_flipSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.stateOddFlipSet_flipSet

/-- info: 'RS.EdgeSubset.mem_highSet_repair_end' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.EdgeSubset.mem_highSet_repair_end

/-- info: 'RS.EdgeSubset.chordCrossingCount_repair_parity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.EdgeSubset.chordCrossingCount_repair_parity

/-- info: 'RS.fourLabel_parity_sep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.fourLabel_parity_sep

/-- info: 'RS.fourLabel_parity_nonsep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.fourLabel_parity_nonsep

/-- info: 'RS.flipSignProd_formula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.flipSignProd_formula

/-- info: 'RS.flipSignProd_of_even' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.flipSignProd_of_even

/-- info: 'RS.EdgeSubset.antiLowSet_transport_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.EdgeSubset.antiLowSet_transport_subset

/-- info: 'RS.symmU_trans' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.symmU_trans

/-- info: 'RS.EdgeSubset.statusDiff_trans' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.EdgeSubset.statusDiff_trans

/-- info: 'RS.EdgeSubset.statusDiff_of_samePairing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.EdgeSubset.statusDiff_of_samePairing

/-- info: 'RS.EdgeSubset.mem_pairFold_antiLow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.EdgeSubset.mem_pairFold_antiLow

/-- info: 'RS.EdgeSubset.antiLow_labels_eq_statusChange' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.EdgeSubset.antiLow_labels_eq_statusChange

/-- info: 'RS.EdgeSubset.antiLowSet_transport_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.EdgeSubset.antiLowSet_transport_eq

/-- info: 'RS.EdgeSubset.antiLowSet_transport_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.EdgeSubset.antiLowSet_transport_card

/-- info: 'RS.EdgeSubset.nonsep_labels_eq_statusChange' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.EdgeSubset.nonsep_labels_eq_statusChange

/-- info: 'RS.diagCrossCount_glue_cross' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.diagCrossCount_glue_cross

/-- info: 'RS.pairedLedgerUnsigned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.pairedLedgerUnsigned

/-- info: 'RS.pairedLedger' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.pairedLedger

/-- info: 'RS.EdgeSubset.stepStatusLedger' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.EdgeSubset.stepStatusLedger

/-- info: 'RS.EdgeSubset.chainStatusLedger' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.EdgeSubset.chainStatusLedger

/-! ### The appendix, for an object

Theorem A.1 as the appendix states it: for an arbitrary object of a
rigid symmetric ℂ-linear category whose tensor powers have
exponentially bounded endomorphism dimensions, the trace zeta
function of every endomorphism is rational of the stated degree.
-/

/--
info: 'RS.frobenius_powHom' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RS.frobenius_powHom

/--
info: 'RS.objectFrobeniusTower' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RS.objectFrobeniusTower

/--
info: 'RS.traceZeta_rational_of_object' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RS.traceZeta_rational_of_object

/--
info: 'RS.scalarTrace_eq_zero_of_isNilpotent' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RS.scalarTrace_eq_zero_of_isNilpotent

/--
info: 'RS.traceZeta_superSpectrum_of_object' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RS.traceZeta_superSpectrum_of_object

/-! ### The appendix's theorems, by type

The axiom audits above fix what these rest on; the pins below fix
what they say — the hypothesis on the object, the threshold, and the
degree bound.
-/

set_option pp.funBinderTypes true in
/--
info: @RS.traceZeta_rational_of_object : ∀ {A : Type u_2} [inst : CategoryTheory.Category.{u_1, u_2} A]
  [inst_1 : CategoryTheory.MonoidalCategory A] [inst_2 : CategoryTheory.SymmetricCategory A]
  [inst_3 : CategoryTheory.Preadditive A] [inst_4 : CategoryTheory.Linear ℂ A]
  [inst_5 : CategoryTheory.MonoidalPreadditive A] [inst_6 : CategoryTheory.MonoidalLinear ℂ A]
  [inst_7 : CategoryTheory.RigidCategory A] (hu : RS.HasScalarUnit A) (X : A)
  [∀ (n : ℕ), Module.Finite ℂ (CategoryTheory.End (RS.tensorPow A X n))] (A₀ : ℝ),
  (∀ (n : ℕ), ↑(Module.finrank ℂ (CategoryTheory.End (RS.tensorPow A X n))) ≤ A₀ ^ n) →
    ∀ (g : CategoryTheory.End X) {s : ℕ},
      2 * Real.exp 1 * √A₀ < ↑s →
        ∃ (Pp : Polynomial ℂ) (Qp : Polynomial ℂ),
          Pp.coeff 0 = 1 ∧
            Qp.coeff 0 = 1 ∧
              Pp.natDegree ≤ s - 1 ∧
                Qp.natDegree ≤ s - 1 ∧
                  IsCoprime Pp Qp ∧ (RS.traceZeta fun (m : ℕ) => (RS.scalarTrace hu X) (g ^ m)) * ↑Qp = ↑Pp
-/
#guard_msgs in
#check @RS.traceZeta_rational_of_object

set_option pp.funBinderTypes true in
/--
info: @RS.traceZeta_superSpectrum_of_object : ∀ {A : Type u_2} [inst : CategoryTheory.Category.{u_1, u_2} A]
  [inst_1 : CategoryTheory.MonoidalCategory A] [inst_2 : CategoryTheory.SymmetricCategory A]
  [inst_3 : CategoryTheory.Preadditive A] [inst_4 : CategoryTheory.Linear ℂ A]
  [inst_5 : CategoryTheory.MonoidalPreadditive A] [inst_6 : CategoryTheory.MonoidalLinear ℂ A]
  [inst_7 : CategoryTheory.RigidCategory A] (hu : RS.HasScalarUnit A) (X : A)
  [∀ (n : ℕ), Module.Finite ℂ (CategoryTheory.End (RS.tensorPow A X n))] (A₀ : ℝ),
  (∀ (n : ℕ), ↑(Module.finrank ℂ (CategoryTheory.End (RS.tensorPow A X n))) ≤ A₀ ^ n) →
    ∀ (g : CategoryTheory.End X) {s : ℕ},
      2 * Real.exp 1 * √A₀ < ↑s →
        ∃ (alpha : Multiset ℂ) (beta : Multiset ℂ),
          alpha.card ≤ s - 1 ∧
            beta.card ≤ s - 1 ∧
              (∀ x ∈ alpha, x ≠ 0) ∧
                (∀ x ∈ beta, x ≠ 0) ∧
                  (∀ x ∈ alpha, x ∉ beta) ∧
                    ∀ (m : ℕ),
                      1 ≤ m →
                        (RS.scalarTrace hu X) (g ^ m) =
                          (Multiset.map (fun (x : ℂ) => x ^ m) alpha).sum -
                            (Multiset.map (fun (x : ℂ) => x ^ m) beta).sum
-/
#guard_msgs in
#check @RS.traceZeta_superSpectrum_of_object

set_option pp.funBinderTypes true in
/--
info: @RS.objectFrobeniusTower : {A : Type u_2} →
  [inst : CategoryTheory.Category.{u_1, u_2} A] →
    [inst_1 : CategoryTheory.MonoidalCategory A] →
      [CategoryTheory.SymmetricCategory A] →
        [inst_3 : CategoryTheory.Preadditive A] →
          [inst_4 : CategoryTheory.Linear ℂ A] →
            [inst_5 : CategoryTheory.MonoidalPreadditive A] →
              [CategoryTheory.MonoidalLinear ℂ A] →
                [CategoryTheory.RigidCategory A] →
                  RS.HasScalarUnit A →
                    (X : A) →
                      (P : RS.SchurPackage) →
                        (A₀ : ℝ) →
                          (∀ (n : ℕ), ↑(Module.finrank ℂ (CategoryTheory.End (RS.tensorPow A X n))) ≤ A₀ ^ n) →
                            RS.FrobeniusTower P (fun (n : ℕ) => CategoryTheory.End (RS.tensorPow A X n)) A₀
                              (CategoryTheory.End X)
-/
#guard_msgs in
#check @RS.objectFrobeniusTower
