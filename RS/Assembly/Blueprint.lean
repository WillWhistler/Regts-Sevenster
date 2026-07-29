import RS.Common.MathlibDeps
import RS.Common.YoungDiagrams
import RS.Classical.SymFun.PowerSums
import RS.Classical.SchurTheory.ColourCycleSum
import RS.Classical.SchurTheory.JTOrtho
import RS.Classical.SchurTheory.SignResolve
import RS.Classical.SchurTheory.NativeFaithful
import RS.Classical.SchurTheory.SquareGrowth
import RS.Classical.SchurTheory.BranchTrace
import RS.Classical.SchurTheory.JTPad
import RS.Classical.SchurTheory.PackageAssembly
import RS.Classical.SchurTheory.Package
import RS.Classical.SchurTheory.PairingPos
import RS.Novel.Envelope.TraceZeta
import RS.Classical.SymFun.ZetaExp
import RS.Classical.SchurTheory.SquareGrowthSharp
import RS.Novel.Envelope.HookConfinementSharp
import RS.Novel.Envelope.SkeinDimBound
import RS.Novel.Skein.PathMatch
import RS.Novel.Envelope.SuperKill
import RS.StatementConverse
import RS.TheoremQuant
import RS.Classical.SymFun.LGVStrict
import RS.Novel.Skein.ClosedAgreement
import RS.Novel.Skein.TransitionMove
import RS.Novel.Skein.GlueRelTransport
import RS.Novel.Skein.DisjSubsetSplit
import RS.Novel.Skein.InterfaceOrderIso
import RS.Novel.Skein.ThroughValue
import RS.Novel.Skein.RelabelInvariance
import RS.Novel.Skein.DisjUnionFactor
import RS.Novel.Skein.GlueCircuitDelta
import RS.Novel.Skein.ChainAgreement
import RS.Novel.Skein.CanonExistence
import RS.Novel.Skein.RepairInvariance
import RS.Novel.Skein.PathLedger
import RS.Novel.Skein.ChordParity
import RS.Novel.Skein.PairingConnectivity
import RS.Novel.Skein.StepLedger
import RS.Novel.Skein.InvolutionCard
import RS.Novel.Skein.ChordCount
import RS.Novel.Skein.AllInternalIndependence
import RS.Novel.Skein.AllInternalAgreement
import RS.Novel.Skein.ConverseAssembly
import RS.Novel.Skein.InterfaceAlternate
import RS.Novel.Skein.ConverseDischarge
import RS.Novel.Skein.ConverseGram
import RS.Novel.Skein.TransposeLedger
import RS.Novel.Skein.TwoPathNonSep
import RS.Novel.Skein.CanonicalFrame
import RS.Novel.Skein.StepFrame
import RS.Novel.Skein.StateFlipSet
import RS.Novel.Skein.StatusSet
import RS.Novel.Skein.CrossingDelta
import RS.Novel.Skein.FlipSignProduct
import RS.Novel.Skein.FlipSignForm
import RS.Novel.Skein.LedgerSets
import RS.Novel.Skein.StepStatus
import RS.Novel.Skein.StepStatusNonsep
import RS.Novel.Skein.PairedAssembly
import RS.Novel.Skein.PropThreeOpen
import RS.Novel.Skein.FourLabelParity
import RS.Novel.Skein.PairingSwap
import RS.Novel.Skein.PairingSignature
import RS.Novel.Skein.PairingValue
import RS.Novel.Skein.LedgerValue
import RS.Novel.Skein.LoopVerify
import RS.Novel.Skein.ThroughIndCFalse
import RS.Novel.Skein.ChordLabels
import RS.Novel.Skein.LabelChords
import RS.Novel.Skein.FibreValue
import RS.Novel.Skein.GlueChords
import RS.Novel.Skein.GluePathMatch
import RS.Novel.Skein.GlueCrossDelta
import RS.Novel.Skein.ClosedCutDispatch
import RS.Novel.Skein.ThroughEdgeCut
import RS.Novel.Skein.RelabelChords
import RS.Novel.Skein.ChordSwapParity
import RS.Classical.SymFun.SuperPowerSums
import RS.Classical.SymFun.RecurrenceFromVanishing
import RS.Classical.SymFun.RationalityFromRecurrence
import RS.Classical.SymFun.HookVanishing
import RS.Classical.Interfaces.SchurPackage
import RS.Novel.Envelope.BlockBounds
import RS.Novel.Envelope.HookConfinement
import RS.Novel.Envelope.KaroubiMonoidal
import RS.Novel.Envelope.MatMonoidal
import RS.Novel.Envelope.MatBraided
import RS.Novel.Envelope.NilpotentTrace
import RS.Novel.Envelope.SemisimpleEnd
import RS.Classical.Super.OrthonormalBasis
import RS.Classical.Super.SuperVect
import RS.Classical.Super.SymplecticBasis
import RS.Novel.Skein.FlagGraph
import RS.Novel.Skein.Composition
import RS.Novel.Skein.FragmentEquiv
import RS.Novel.Skein.CompositionEquiv
import RS.Novel.Skein.StrandBundle
import RS.Novel.Skein.IdentityLaw
import RS.Novel.Skein.IdentityLawRight
import RS.Novel.Skein.ConnectionRank
import RS.Novel.Skein.HomSpaces
import RS.Novel.Skein.Multiplicativity
import RS.Novel.Skein.Eulerian
import RS.Novel.Skein.TransitionExists
import RS.Novel.Skein.GlueAmbient
import RS.Novel.Skein.GlueComm
import RS.Novel.Skein.CloseRotate
import RS.Novel.Skein.CloseRotateLeft
import RS.Novel.Skein.InterfaceShift
import RS.Novel.Skein.PairCloseComm
import RS.Novel.Skein.SimpleUnit
import RS.Novel.Skein.SkeinIdeal
import RS.Novel.Skein.SkeinIdealLeft
import RS.Novel.Skein.HomCompose
import RS.Novel.Skein.SkeinCategory
import RS.Novel.Skein.HomTraceNondegenerate
import RS.Novel.Skein.SkeinCatInstance
import RS.Novel.Skein.SkeinLinear
import RS.Novel.Skein.HomTraceCyclic
import RS.Novel.Skein.StarDecomposition
import RS.Novel.Skein.ComposeAssoc
import RS.Novel.Skein.ComposeNormal
import RS.Novel.Skein.GlueFold
import RS.Novel.Skein.MixedPartition
import RS.Novel.Skein.PermFragment
import RS.Novel.Skein.PermCompose
import RS.Novel.Skein.Trace
import RS.Novel.Skein.TraceCyclic
import RS.Novel.Skein.TraceNondegenerate
import RS.Novel.Skein.TensorIdeal
import RS.Novel.Skein.TensorComm
import RS.Novel.Skein.HomTensor
import RS.Novel.Skein.TensorAssoc
import RS.Novel.Skein.TensorUnit
import RS.Novel.Skein.PartialCloseTensor
import RS.Novel.Skein.CloseUnion
import RS.Novel.Skein.ComposeRelabel
import RS.Novel.Skein.PartialCloseCompose
import RS.Novel.Skein.ScalarClass
import RS.StatementForward
import RS.Novel.Extraction.CircleValue
import RS.Novel.Extraction.CoordIso
import RS.Novel.Extraction.Coordinates
import RS.Novel.Extraction.CopairUnique
import RS.Novel.Extraction.SnakeTransport
import RS.Novel.Extraction.Nondegenerate
import RS.Novel.Extraction.StdDuality
import RS.Novel.Extraction.StdRigid
import RS.Novel.Extraction.StdSuper
import RS.Classical.Interfaces.DeligneBridge
import RS.Classical.Interfaces.DelignePackage
import RS.Classical.Interfaces.DeligneTheorem
import RS.Classical.Interfaces.FibreTransport
import RS.Classical.Interfaces.EulerianIndependence
import RS.Novel.Skein.StarTrace
import RS.Novel.Skein.SnakeClasses
import RS.Classical.Super.ColourFormMatch
import RS.Classical.Super.ColourPairing
import RS.Classical.Super.ColourPairingSymm
import RS.Novel.Skein.TensorInterchange
import RS.Novel.Skein.MonoidalInstance
import RS.Novel.Skein.BraidedInstance
import RS.Novel.Skein.ExactPairingInstance
import RS.Novel.Skein.StarCompClass
import RS.Novel.Coordinates.OmegaTransport
import RS.Novel.Coordinates.SortFactor
import RS.Novel.Coordinates.StarClassFactor
import RS.Novel.Coordinates.OmegaTensor
import RS.Novel.Coordinates.OmegaStarVec
import RS.Novel.Coordinates.CircleModel
import RS.Novel.Coordinates.BraidWord
import RS.Novel.Coordinates.StarSymm
import RS.Novel.Coordinates.ModelStarVec
import RS.Novel.Coordinates.ParameterModel
import RS.Classical.Super.ColourConjStep
import RS.Classical.Super.ColourWord
import RS.Classical.Super.WordSignPerm
import RS.Classical.Super.ColourConjTop
import RS.Classical.Super.ColourAction
import RS.Novel.Coordinates.ModelPermCoord
import RS.Novel.Coordinates.CapClosed
import RS.Novel.Coordinates.MasterSum
import RS.Novel.Coordinates.StarPerm
import RS.Novel.Coordinates.StarRepeat
import RS.Novel.Coordinates.Reindex
import RS.Novel.Coordinates.FibreParam
import RS.Novel.Coordinates.BlockParity
import RS.Novel.Coordinates.ReindexVanish
import RS.Novel.Coordinates.BetaDiagForm
import RS.Novel.Coordinates.ReindexBij
import RS.Novel.Coordinates.BlockData
import RS.Novel.Coordinates.RepFlag
import RS.Novel.Coordinates.BetaData
import RS.Novel.Coordinates.OddFlip
import RS.Novel.Coordinates.BlockAlign
import RS.Novel.Coordinates.PatternInv
import RS.Novel.Coordinates.ListSignPerm
import RS.Novel.Coordinates.OutSignEdges
import RS.Novel.Coordinates.EdgeSign
import RS.Novel.Coordinates.OddListMultiset
import RS.Novel.Coordinates.OddSignProd
import RS.Novel.Coordinates.BetaFlip
import RS.Novel.Coordinates.CircuitCount
import RS.Novel.Coordinates.PairEnum
import RS.Novel.Coordinates.FlagEnum
import RS.Novel.Coordinates.IndexPerm
import RS.Novel.Coordinates.TauKey
import RS.Novel.Coordinates.CanonPerm
import RS.Novel.Coordinates.BlockCanon
import RS.Novel.Coordinates.VertexValue
import RS.Novel.Coordinates.BlockOddList
import RS.Novel.Coordinates.VertexSign
import RS.Novel.Coordinates.TauCount
import RS.Novel.Coordinates.GlobalSlotList
import RS.Novel.Coordinates.ChainLists
import RS.Novel.Coordinates.ConcatSign
import RS.Novel.Coordinates.SignPair
import RS.Novel.Coordinates.RiffleSign
import RS.Novel.Coordinates.NFDef
import RS.Novel.Coordinates.RegroupSign
import RS.Novel.Coordinates.CoreParity
import RS.Novel.Coordinates.NFValue
import RS.Novel.Coordinates.ReindexHeart
import RS.TheoremForward
import RS.Novel.Coordinates.CapVal
import RS.Novel.Coordinates.CapSplit
import RS.Novel.Coordinates.ClosedTransition
import RS.Novel.Coordinates.ModelCoord
import RS.Novel.Coordinates.OneBasis
import RS.Novel.Coordinates.EvLeaf
import RS.Novel.Coordinates.CapExpansion
import RS.Novel.Coordinates.CapPeelSplit
import RS.Novel.Coordinates.BasisCoord
import RS.Novel.Coordinates.BetaDiag
import RS.Novel.Coordinates.SlotPairing
import RS.Novel.Coordinates.TopBraidMerge
import RS.Novel.Coordinates.TwoBasis
import RS.Novel.Envelope.EnvDelignePackage

/-!
# Blueprint: the axiom audit

Every main theorem of the development carries a pinned
`#print axioms` line: an axiom set drifting from the whitelist
`[propext, Classical.choice, Quot.sound]` is a compile error, not a
reading exercise.  A new theorem worth auditing gets a pinned line.

**How to read it.**  The sections below follow the forward proof in
the order it is built, from hook vanishing to the theorem itself.
Each pin names one theorem; the section it sits in says what that
theorem contributes.  The converse is audited in
`BlueprintConverse.lean`, the symmetric-group input in
`BlueprintSchur.lean`, and the statement surface — every definition
the summits are phrased in — in `BlueprintStatement.lean`.
-/

/-! ### Hook vanishing and the power sums

A tower whose hook-confined characters vanish has vanishing
super power sums, which is what makes the trace zeta rational.
-/

/-- info: 'RS.superPowerSums_of_hook_vanishing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.superPowerSums_of_hook_vanishing

/-- info: 'RS.powerSums_zero_of_eventually_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.powerSums_zero_of_eventually_zero

/-! ### Hook confinement and nilpotent traces

Exponentially bounded growth confines the surviving Young diagrams
to a hook, nilpotents then have vanishing trace, and the trace
criterion makes every endomorphism algebra semisimple.
-/

/-- info: 'RS.PermTower.hook_confinement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.PermTower.hook_confinement

/-- info: 'RS.FrobeniusTower.traceA_eq_zero_of_isNilpotent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.FrobeniusTower.traceA_eq_zero_of_isNilpotent

/-- info: 'RS.isSemisimpleRing_of_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.isSemisimpleRing_of_trace

/-! ### The classical bases

The symplectic and orthonormal standard bases the super model is
written in.
-/

/-- info: 'RS.exists_symplectic_basis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.exists_symplectic_basis

/-- info: 'RS.exists_orthonormal_basis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.exists_orthonormal_basis

/-! ### Definition 5 and its transport

The mixed partition value of an edge subset, and its invariance
under a fragment equivalence.
-/

/-- info: 'RS.EdgeSubset.mixedSummand_transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.EdgeSubset.mixedSummand_transport

/-- info: 'RS.mixedPartition_transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.mixedPartition_transport

/-! ### The hypothesis class

The edge-rank hypothesis bounds the dimension of a row span; the
literature bounds the ranks of the finite submatrices of the
connection matrix.  The two are the same condition.
-/

/-- info: 'RS.edgeRankBounded_iff_submatrixRank' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.edgeRankBounded_iff_submatrixRank

/-! ### The gluing calculus

Gluing a list of label pairs: permuting the list, appending,
normalising an interface, and the existence of transition data.
-/

/-- info: 'RS.Fragment.glueListPerm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.Fragment.glueListPerm

/-- info: 'RS.glueInterfaceNormal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.glueInterfaceNormal

/-- info: 'RS.Fragment.glueListAppend' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.Fragment.glueListAppend

/-- info: 'RS.EdgeRankParameter.val_union' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.EdgeRankParameter.val_union

/-- info: 'RS.EdgeSubset.exists_transition_orientation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.EdgeSubset.exists_transition_orientation

/-- info: 'RS.RegtsSevensterStatement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.RegtsSevensterStatement

/-- info: 'RS.composeStrandBundleLeft' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.composeStrandBundleLeft

/-- info: 'RS.Fragment.gluePairComm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.Fragment.gluePairComm

/-- info: 'RS.composeStrandBundleRight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.composeStrandBundleRight

/-! ### Coordinates and the standard model

Contraction families, the standard form and copairing, and the
coordinates a nondegenerate pairing gives.
-/

/-- info: 'RS.exists_coordinates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.exists_coordinates

/-- info: 'RS.exists_contraction_families' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.exists_contraction_families

/-- info: 'RS.exists_coordinates_of_snake' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.exists_coordinates_of_snake

/-- info: 'RS.exists_std_iso' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.exists_std_iso

/-- info: 'RS.stdCopair_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.stdCopair_unique

/-- info: 'RS.exists_std_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.exists_std_model

/-- info: 'RS.stdForm_comp_stdCopair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.stdForm_comp_stdCopair

/-! ### Gluing across a disjoint union

The glue list distributes over a disjoint union and commutes with
swaps and folds — the associativity engine of the category.
-/

/-- info: 'RS.Fragment.glueListDisjUnionLeft' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.Fragment.glueListDisjUnionLeft

/-- info: 'RS.Fragment.glueListDisjUnionRight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.Fragment.glueListDisjUnionRight

/-- info: 'RS.Fragment.glueListSwap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.Fragment.glueListSwap

/-- info: 'RS.composeAssoc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.composeAssoc

/-- info: 'RS.pairCloseComposeRotate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.pairCloseComposeRotate

/-- info: 'RS.pairCloseComposeRotateLeft' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.pairCloseComposeRotateLeft

/-- info: 'RS.composeFinsupp_ker_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.composeFinsupp_ker_left

/-- info: 'RS.composeFinsupp_ker_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.composeFinsupp_ker_right

/-- info: 'RS.HomSpace.comp_ofFragment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.HomSpace.comp_ofFragment

/-- info: 'RS.HomSpace.comp_assoc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.HomSpace.comp_assoc

/-- info: 'RS.HomSpace.comp_id_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.HomSpace.comp_id_left

/-- info: 'RS.HomSpace.comp_id_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.HomSpace.comp_id_right

/-- info: 'RS.HomSpace.eq_zero_of_traces_vanish' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.HomSpace.eq_zero_of_traces_vanish

/-- info: 'RS.skeinCategory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.skeinCategory

/-- info: 'RS.starDecomposition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.starDecomposition

/-- info: 'RS.homSpace_zero_spanned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.homSpace_zero_spanned

/-- info: 'RS.interfaceShift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.interfaceShift

/-- info: 'RS.Fragment.pairCloseComm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.Fragment.pairCloseComm

/-! ### The exact pairing

The self-duality of the standard model, and that it is braided.
-/

/-- info: 'RS.ExactPairing.map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.ExactPairing.map

/-- info: 'RS.braided_std_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.braided_std_model

/-! ### The trace calculus

Closing a fragment against the strand bundle: relabels cross it,
tensors absorb, and permutation fragments compose.
-/

/-- info: 'RS.pairCloseRelabel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.pairCloseRelabel

/-- info: 'RS.fragTrace_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.fragTrace_comm

/-- info: 'RS.permFragmentCompose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.permFragmentCompose

/-- info: 'RS.mem_ker_of_traces_vanish' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.mem_ker_of_traces_vanish

/-- info: 'RS.pairCloseTensorAbsorb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.pairCloseTensorAbsorb

/-- info: 'RS.tensorFinsupp_ker_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.tensorFinsupp_ker_left

/-- info: 'RS.tensorFinsupp_ker_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.tensorFinsupp_ker_right

/-- info: 'RS.HomSpace.tensor_ofFragment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.HomSpace.tensor_ofFragment

/-- info: 'RS.tensorFragmentAssoc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.tensorFragmentAssoc

/-- info: 'RS.tensorFragmentUnitLeft' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.tensorFragmentUnitLeft

/-- info: 'RS.tensorFragmentUnitRight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.tensorFragmentUnitRight

/-! ### The braided envelope

The Karoubi and matrix envelopes inherit the braiding and its
symmetry.
-/

/-- info: 'RS.karoubiBraided' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.karoubiBraided

/-- info: 'RS.karoubiSymmetric' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.karoubiSymmetric

/-- info: 'RS.matBraided' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.matBraided

/-- info: 'RS.matSymmetric' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.matSymmetric

/-! ### The skein category

Linear, monoidal and rigid structure on the skein category, and
the trace map it carries.
-/

/-- info: 'RS.skeinPreadditive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.skeinPreadditive

/-- info: 'RS.skeinLinear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.skeinLinear

/-- info: 'RS.HomSpace.traceMap_comp_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.HomSpace.traceMap_comp_comm

/-- info: 'RS.partialCloseTensor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.partialCloseTensor

/-- info: 'RS.pairCloseUnionRight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.pairCloseUnionRight

/-- info: 'RS.fragTrace_tensor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.fragTrace_tensor

/-- info: 'RS.composeRelabelOut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.composeRelabelOut

/-- info: 'RS.composePermFragment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.composePermFragment

/-- info: 'RS.partialCloseEqCompose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.partialCloseEqCompose

/-- info: 'RS.ofFragment_eq_smul_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.ofFragment_eq_smul_empty

/-- info: 'RS.pairCloseStrandBundle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.pairCloseStrandBundle

/-- info: 'RS.starDecomposition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.starDecomposition

/-- info: 'RS.snake_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.snake_left

/-- info: 'RS.snake_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.snake_right

/-- info: 'RS.braid_comp_evClass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.braid_comp_evClass

/-- info: 'RS.Fragment.tensorComposeInterchange' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.Fragment.tensorComposeInterchange

/-- info: 'RS.skeinMonoidal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.skeinMonoidal

/-- info: 'RS.skeinBraided' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.skeinBraided

/-- info: 'RS.skeinSymmetric' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.skeinSymmetric

/-- info: 'RS.strandExactPairing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.strandExactPairing

/-- info: 'RS.strand_ev_symmetry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.strand_ev_symmetry

/-- info: 'RS.star_comp_class' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.star_comp_class

/-! ### The coordinate model

The fibre functor's image of a star, the standard model it is
identified with, and the transport between them.
-/

/-- info: 'RS.omega_star_scalar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.omega_star_scalar

/-- info: 'RS.skein_std_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.skein_std_model

/-- info: 'RS.starUnionFactor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.starUnionFactor

/-- info: 'RS.starClass_factor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.starClass_factor

/-- info: 'RS.omegaVec_tensor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.omegaVec_tensor

/-- info: 'RS.parameter_star_factor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.parameter_star_factor

/-- info: 'RS.circleVal_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.circleVal_model

/-- info: 'RS.stdFromOmega_stdToOmega' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.stdFromOmega_stdToOmega

/-- info: 'RS.adjWord_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.adjWord_spec

/-- info: 'RS.stdToOmega_powBraid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.stdToOmega_powBraid

/-- info: 'RS.stdToOmega_bmc_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.stdToOmega_bmc_perm

/-- info: 'RS.bundleCapClass_peel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.bundleCapClass_peel

/-- info: 'RS.point_cotensor' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms RS.point_cotensor

/-- info: 'RS.omegaFun_tensor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.omegaFun_tensor

/-- info: 'RS.evForm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.evForm

/-- info: 'RS.vertexStarClass_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.vertexStarClass_perm

/-- info: 'RS.stdToOmega_merge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.stdToOmega_merge

/-- info: 'RS.stdToOmega_modelStarVec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.stdToOmega_modelStarVec

/-- info: 'RS.toColour_whisker' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.toColour_whisker

/-- info: 'RS.parameter_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.parameter_model

/-- info: 'RS.colourExtend_colourSwap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.colourExtend_colourSwap

/-- info: 'RS.colourSwapWord_evenMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.colourSwapWord_evenMap

/-- info: 'RS.parameter_capVal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.parameter_capVal

/-- info: 'RS.ClosedFragment.eulerian_transition_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.ClosedFragment.eulerian_transition_nonempty

/-- info: 'RS.omegaFun_capTensor_merge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.omegaFun_capTensor_merge

/-- info: 'RS.omegaFun_tensor_oddPair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.omegaFun_tensor_oddPair

/-- info: 'RS.colourMerge_coord' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.colourMerge_coord

/-- info: 'RS.colourMerge_coord_oddPair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.colourMerge_coord_oddPair

/-- info: 'RS.coordOf_modelStarVec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.coordOf_modelStarVec

/-- info: 'RS.evenBasisVec_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.evenBasisVec_split

/-- info: 'RS.evFormOdd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.evFormOdd

/-- info: 'RS.stdToOmega_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.stdToOmega_one

/-- info: 'RS.stdToOmega_one_even' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.stdToOmega_one_even

/-- info: 'RS.stdToOmega_one_odd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.stdToOmega_one_odd

/-- info: 'RS.evenBasisVec_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.evenBasisVec_one

/-- info: 'RS.oddBasisVec_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.oddBasisVec_one

/-- info: 'RS.stdForm_evenPair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.stdForm_evenPair

/-- info: 'RS.stdForm_oddPair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.stdForm_oddPair

/-- info: 'RS.omegaFun_ev_basis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.omegaFun_ev_basis

/-- info: 'RS.capVal_expansion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.capVal_expansion

/-- info: 'RS.splitCapVal_expansion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.splitCapVal_expansion

/-- info: 'RS.splitCapVal_merge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.splitCapVal_merge

/-- info: 'RS.capVal_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.capVal_succ

/-- info: 'RS.coordOf_evenBasisVec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.coordOf_evenBasisVec

/-- info: 'RS.splitCapVal_oddMerge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.splitCapVal_oddMerge

/-- info: 'RS.peelColour_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms RS.peelColour_spec

/-- info: 'RS.eq_peelColour_of' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms RS.eq_peelColour_of

/-- info: 'RS.peelColour_isEven' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.peelColour_isEven

/-- info: 'RS.pairing_starFlagEnum_symm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.pairing_starFlagEnum_symm

/-- info: 'RS.powMerge_topBraid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.powMerge_topBraid

/-- info: 'RS.wordSign_eq_oddInversions' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.wordSign_eq_oddInversions

/-- info: 'RS.toColour_topBraid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.toColour_topBraid

/-- info: 'RS.toColour_powBraid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.toColour_powBraid

/-- info: 'RS.toColour_powBraidWord' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.toColour_powBraidWord

/-! ### The master colour sum

The parameter as a sum over colourings: the star coordinates, the
diagonal cap pairing, every sign family, and the reindexing that
turns the sum into Definition 5.
-/

/-- info: 'RS.wordPerm_adjWord' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.wordPerm_adjWord

/-- info: 'RS.coordOf_modelPermMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.coordOf_modelPermMap

/-- info: 'RS.coordOf_modelPermMap'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.coordOf_modelPermMap'

/-- info: 'RS.capVal_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.capVal_closed

/-- info: 'RS.parameter_colour_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.parameter_colour_sum

/-- info: 'RS.starVec_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.starVec_perm

/-- info: 'RS.stdFromOmega_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.stdFromOmega_perm

/-- info: 'RS.starCoord_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.starCoord_perm

/-- info: 'RS.oddInversions_adjacent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.oddInversions_adjacent

/-- info: 'RS.starCoord_repeat_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.starCoord_repeat_zero

/-- info: 'RS.parameter_masterSummand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.parameter_masterSummand

/-- info: 'RS.masterSum_partition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.masterSum_partition

/-- info: 'RS.colourFlags_pairing_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.colourFlags_pairing_mem

/-- info: 'RS.colourFlags_colouringOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.colourFlags_colouringOf

/-- info: 'RS.EdgeSubset.card_even' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.EdgeSubset.card_even

/-- info: 'RS.colouringOf_isEven' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.colouringOf_isEven

/-- info: 'RS.colouringOf_diagonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.colouringOf_diagonal

/-- info: 'RS.blockRestrict_parity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.blockRestrict_parity

/-- info: 'RS.masterSummand_vanish_of_block_odd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.masterSummand_vanish_of_block_odd

/-- info: 'RS.masterSummand_vanish_of_not_eulerian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.masterSummand_vanish_of_not_eulerian

/-- info: 'RS.mem_colourFlags_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.mem_colourFlags_iff

/-- info: 'RS.starFlagEnum_pairing_low' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.starFlagEnum_pairing_low

/-- info: 'RS.starFlagEnum_pairing_high' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.starFlagEnum_pairing_high

/-- info: 'RS.oddDataOf_constancy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.oddDataOf_constancy

/-- info: 'RS.evenDataOf_constancy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.evenDataOf_constancy

/-- info: 'RS.betaDiag_eq_betaColour' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.betaDiag_eq_betaColour

/-- info: 'RS.masterSummand_vanish_of_impure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.masterSummand_vanish_of_impure

/-- info: 'RS.masterSummand_vanish_of_not_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.masterSummand_vanish_of_not_closed

/-- info: 'RS.colouringOf_reconstruct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.colouringOf_reconstruct

/-- info: 'RS.oddColouringOf_colouringOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.oddColouringOf_colouringOf

/-- info: 'RS.evenColouringOf_colouringOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.evenColouringOf_colouringOf

/-- info: 'RS.masterSummand_vanish_of_not_diagonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.masterSummand_vanish_of_not_diagonal

/-- info: 'RS.pairPure_of_pattern_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.pairPure_of_pattern_closed

/-- info: 'RS.fibreSum_eq_dataSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.fibreSum_eq_dataSum

/-- info: 'RS.koszulCrossings_colouringOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.koszulCrossings_colouringOf

/-- info: 'RS.image_blockFlag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.image_blockFlag

/-- info: 'RS.blockRestrict_colouringOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.blockRestrict_colouringOf

/-- info: 'RS.blockRestrict_colouringOf_isRight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.blockRestrict_colouringOf_isRight

/-- info: 'RS.repFlag_pairing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.repFlag_pairing

/-- info: 'RS.outRepSet_pairing_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.outRepSet_pairing_mem

/-- info: 'RS.colourFormEntry_inr_partner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.colourFormEntry_inr_partner

/-- info: 'RS.betaDiag_colouringOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.betaDiag_colouringOf

/-- info: 'RS.evenColoursAt_blockVertex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.evenColoursAt_blockVertex

/-- info: 'RS.EdgeSubset.OddColouring.sum_flip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.EdgeSubset.OddColouring.sum_flip

/-- info: 'RS.blockRestrict_colouringOfFlip_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.blockRestrict_colouringOfFlip_mem

/-- info: 'RS.map_flagsAt_blockVertex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.map_flagsAt_blockVertex

/-- info: 'RS.oddInversions_colouringOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.oddInversions_colouringOf

/-- info: 'RS.sortSign_ofFn_comp_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.sortSign_ofFn_comp_perm

/-- info: 'RS.prod_out_sign_eq_prod_edges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.prod_out_sign_eq_prod_edges

/-- info: 'RS.edge_sign_sector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.edge_sign_sector

/-- info: 'RS.oddListAt_coe_multiset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.oddListAt_coe_multiset

/-- info: 'RS.prod_oddSignAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.prod_oddSignAt

/-- info: 'RS.betaDiag_colouringOfFlip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.betaDiag_colouringOfFlip

/--
info: 'RS.EdgeSubset.TransitionSystem.circuitCount_eq_orbitCount_outPerm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms RS.EdgeSubset.TransitionSystem.circuitCount_eq_orbitCount_outPerm

/-- info: 'RS.EdgeSubset.TransitionSystem.neg_one_pow_circuitCount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.EdgeSubset.TransitionSystem.neg_one_pow_circuitCount

/-- info: 'RS.oddListAt_eq_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.oddListAt_eq_map

/-- info: 'RS.pairFlagList_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.pairFlagList_nodup

/-- info: 'RS.mem_blockOddFlagList_iff_pairFlagList' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.mem_blockOddFlagList_iff_pairFlagList

/-- info: 'RS.prod_blockVertex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.prod_blockVertex

/-- info: 'RS.sortSign_map_listIndexPerm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.sortSign_map_listIndexPerm

/-- info: 'RS.sign_listIndexPerm_trans' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.sign_listIndexPerm_trans

/-- info: 'RS.sortSign_pairFlagList_key' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.sortSign_pairFlagList_key

/-- info: 'RS.exists_canonPerm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.exists_canonPerm

/-- info: 'RS.oddListOf_blockRestrict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.oddListOf_blockRestrict

/-- info: 'RS.evenMultisetOf_blockRestrict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.evenMultisetOf_blockRestrict

/-- info: 'RS.starCoord_block_flip_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.starCoord_block_flip_nodup

/-- info: 'RS.starCoord_block_flip_not_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.starCoord_block_flip_not_nodup

/-- info: 'RS.oddListOf_blockRestrict_eq_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.oddListOf_blockRestrict_eq_map

/-- info: 'RS.vertex_sign_collapse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.vertex_sign_collapse

/-- info: 'RS.patternOddInv_eq_inversions' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.patternOddInv_eq_inversions

/-- info: 'RS.sortSign_globalPairList' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.sortSign_globalPairList

/-- info: 'RS.sign_listIndexPerm_slot_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.sign_listIndexPerm_slot_edge

/-- info: 'RS.sign_listIndexPerm_edge_oriented' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.sign_listIndexPerm_edge_oriented

/-- info: 'RS.hMaster_vertex_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.hMaster_vertex_nodup

/-- info: 'RS.defFiveNF_eq_flip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.defFiveNF_eq_flip

/-- info: 'RS.sign_listIndexPerm_oriented_matched' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.sign_listIndexPerm_oriented_matched

/-- info: 'RS.sign_listIndexPerm_matched_global' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.sign_listIndexPerm_matched_global

/-- info: 'RS.core_parity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.core_parity

/-- info: 'RS.grand_parity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.grand_parity

/-- info: 'RS.masterSummand_colouringOfFlip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.masterSummand_colouringOfFlip

/-- info: 'RS.fibreSum_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.fibreSum_eq

/-- info: 'RS.parameter_eq_mixedPartition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.parameter_eq_mixedPartition

/-- info: 'RS.hMaster_colouringOfFlip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.hMaster_colouringOfFlip

/-- info: 'RS.mixedSummand_eq_nf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.mixedSummand_eq_nf

/-- info: 'RS.eulerian_independence_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.eulerian_independence_closed

/-- info: 'RS.mixedValue_eq_summand_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.mixedValue_eq_summand_closed

/-! ### Deligne's hypotheses for the envelope

Each hypothesis of the cited theorem, discharged for the concrete
envelope, and the package they assemble into.
-/

/-- info: 'RS.env_deligneSemisimple' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.env_deligneSemisimple

/-- info: 'RS.env_deligneGenerated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.env_deligneGenerated

/-- info: 'RS.env_deligneModerateGrowth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.env_deligneModerateGrowth

/-- info: 'RS.env_delignePackage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.env_delignePackage

/-- info: 'RS.skein_delignePackage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.skein_delignePackage

/-! ### The forward theorem -/

/-- info: 'RS.regts_sevenster_conditional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.regts_sevenster_conditional
