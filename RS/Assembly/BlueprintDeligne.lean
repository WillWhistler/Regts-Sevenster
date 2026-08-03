import RS.Summit

/-!
# Audit: Deligne's theorem and the unconditional summit

The pinned axiom checks for the theorem that was formerly assumed
and for the statements that no longer assume it.  Each `#guard_msgs`
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

/-- info: 'RS.regts_sevenster_characterisation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.regts_sevenster_characterisation

/-- info: 'RS.regts_sevenster_quant_characterisation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RS.regts_sevenster_quant_characterisation

end RS
