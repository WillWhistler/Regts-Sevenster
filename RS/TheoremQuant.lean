import RS.Classical.Interfaces.SectorDischarge
import RS.Classical.SymFun.LGVStrict

/-!
# The quantitative theorem, one determinant from Deligne-only

The sector bound is a theorem given the negated square Schur
nonvanishing, so the quantitative Regts–Sevenster statement rests
on Deligne's theorem and one binomial determinant.
-/

namespace RS

/-- **THE QUANTITATIVE REGTS–SEVENSTER THEOREM, CONDITIONAL ON
DELIGNE AND THE BINOMIAL DETERMINANT.** -/
theorem regts_sevenster_quant_of_detPos
    (H : SquareBinomialDetPos)
    (hDeligne : DeligneTheoremStatement.{1, 1}) :
    RegtsSevensterStatementQuant :=
  regts_sevenster_quant_of_sector
    (squareSectorBound_of_detPos H) hDeligne

/-- **THE QUANTITATIVE REGTS–SEVENSTER THEOREM, CONDITIONAL ON
DELIGNE ALONE**: the binomial determinant is a theorem
(Lindström–Gessel–Viennot), so every graph parameter with
edge-connection rank at most `R ^ t` is the mixed partition
function of a functional with both dimensions at most `⌊2eR⌋`,
assuming only Deligne's theorem on tensor categories. -/
theorem regts_sevenster_quant_deligne_only
    (hDeligne : DeligneTheoremStatement.{1, 1}) :
    RegtsSevensterStatementQuant :=
  regts_sevenster_quant_of_detPos squareBinomialDetPos hDeligne

end RS
