import RS.Summit

/-!
# Audit: Deligne's theorem and the unconditional summit

The pinned axiom checks for Deligne’s theorem and the unconditional
summit statements. Each `#guard_msgs`
fails the build if the axiom set changes, so the claim that these
depend on nothing beyond `propext`, `Classical.choice` and
`Quot.sound` is checked rather than asserted.
-/

namespace RS

/-! ### Deligne's theorem -/

/-- info: 'RS.deligne_theorem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.deligne_theorem

/-- info: 'RS.braidedFibreHypothesis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.braidedFibreHypothesis

/-- info: 'RS.exists_splitting_simple_algebra_doubled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.exists_splitting_simple_algebra_doubled

/-- info: 'RS.exists_simple_quotient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.exists_simple_quotient

/-! ### The summit, unconditionally -/

/-- info: 'RS.regts_sevenster' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.regts_sevenster

/-- info: 'RS.regts_sevenster_quant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.regts_sevenster_quant

/-- info: 'RS.regts_sevenster_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.regts_sevenster_total

/-- info: 'RS.regts_sevenster_characterisation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.regts_sevenster_characterisation

/-- info: 'RS.regts_sevenster_quant_characterisation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.regts_sevenster_quant_characterisation

/-! ### Minimum dimensions, growth and padding -/

/-- info: 'RS.minimumColourDimension_le_of_represents' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.minimumColourDimension_le_of_represents

/-- info: 'RS.TotalBoundedMixedModel.dimension_eq_minimum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.TotalBoundedMixedModel.dimension_eq_minimum

/-- info: 'RS.stdModel_dimension_eq_minimum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.stdModel_dimension_eq_minimum

/-- info: 'RS.stdModel_connectionRank_growth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.stdModel_connectionRank_growth

/-- info: 'RS.MixedColourEmbedding.mixedPartition_extendColours' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.MixedColourEmbedding.mixedPartition_extendColours

/-- info: 'RS.MixedFunctional.padColours_represents' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.MixedFunctional.padColours_represents

/-- info: 'RS.TotalBoundedMixedModel.even_dimension_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.TotalBoundedMixedModel.even_dimension_eq

/-- info: 'RS.TotalBoundedMixedModel.half_odd_dimension_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.TotalBoundedMixedModel.half_odd_dimension_eq

/-- info: 'RS.regts_sevenster_minimum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.regts_sevenster_minimum

/-- info: 'RS.regts_sevenster_rank_growth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.regts_sevenster_rank_growth

/-- info: 'RS.regts_sevenster_prescribed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.regts_sevenster_prescribed

end RS
