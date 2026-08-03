import RS.Novel.Coordinates.ReindexHeart
import RS.Novel.Envelope.EnvDelignePackage
import RS.Classical.SchurTheory.Package

/-!
# The Regts–Sevenster theorem, forward direction

The summit of the forward direction, in two forms: conditional on
the classical symmetric-group input and Deligne's theorem, which
exhibits the dependency structure, and conditional on Deligne
alone, which is the theorem of record.  The two differ only in
whether the Schur package is taken as a hypothesis or supplied by
`schurPackage`.
-/

namespace RS

open CategoryTheory

/-- **The Regts–Sevenster theorem, two-input form**: from the
classical symmetric-group representation theory (the Schur
package — itself a theorem of this development, `schurPackage`,
instantiated below) and Deligne's theorem on tensor categories,
every graph parameter with exponentially bounded edge-connection
rank is a mixed partition function.  This form exhibits the
dependency structure; the theorem of record is
`regts_sevenster_deligne_only`. -/
theorem regts_sevenster_conditional
    (hSchur : Nonempty SchurPackage.{1})
    (hDeligne : DeligneTheoremStatement.{1, 1}) :
    RegtsSevensterStatement := by
  intro R f
  obtain ⟨S⟩ := hSchur
  obtain ⟨P⟩ := skein_delignePackage f S hDeligne
  obtain ⟨k, ℓ, e, e', he'e, hee', hform, hcopair⟩ :=
    skein_std_model f P
  refine ⟨k, ℓ, hRS f P e', fun W => ?_⟩
  exact parameter_eq_mixedPartition f P e e' W
    hee' he'e hform hcopair

/-- **THE REGTS–SEVENSTER THEOREM, CONDITIONAL ON DELIGNE
ALONE**: the classical symmetric-group input is a theorem
(`schurPackage`), so every graph parameter with exponentially
bounded edge-connection rank is a mixed partition function
assuming only Deligne's theorem on tensor categories. -/
theorem regts_sevenster_deligne_only
    (hDeligne : DeligneTheoremStatement.{1, 1}) :
    RegtsSevensterStatement :=
  regts_sevenster_conditional ⟨schurPackage⟩ hDeligne

end RS
