import RS.Classical.Deligne.SplittingAlgebra
import RS.Classical.Deligne.IndLocallyMixed
import RS.Classical.Deligne.IndSplitSection
import RS.Classical.Deligne.IndUnitNonzero
import RS.Classical.Deligne.ScalarUnitInd

/-!
# The splitting algebra of a Schur-killed category

Every object of a category all of whose objects are killed by some
Schur functor is locally mixed after the Ind-embedding, and every
short exact sequence splits after base change; so the universal
algebra of `RS.exists_splitting_algebra` splits every embedded
object and every embedded short exact sequence at once.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v

variable {C : Type v} [SmallCategory C] [MonoidalCategory C]
  [SymmetricCategory C] [Abelian C] [RigidCategory C]
  [MonoidalPreadditive C]

/-- **The fibre algebra of a Schur-killed category.** -/
theorem exists_fibre_algebra (ψ : ℂ ≃+* End (𝟙_ C))
    (P : SchurPackage.{v}) (P₀ : SchurPackage.{0})
    (L : OddLine (Ind C))
    (hkill : letI := linearOfScalarUnit ψ
      ∀ Z : C, ∃ lam : YoungDiagram, SchurKilled P Z lam) :
    letI := linearOfScalarUnit ψ
    letI := monoidalLinearOfScalarUnitBraided ψ
    letI := linearOfScalarUnit (indScalarUnit ψ)
    letI := monoidalLinearOfScalarUnitBraided (indScalarUnit ψ)
    ∃ (𝔸 : Ind C) (_ : MonObj 𝔸) (_ : IsCommMonObj 𝔸),
      MonObj.one (X := 𝔸) ≠ 0 ∧
      SplitsOn L 𝔸 (indOf : C ⥤ Ind C) ∧
      (∀ T : ShortComplex C, T.ShortExact →
        ∃ s : freeMod 𝔸 ((T.map (indOf : C ⥤ Ind C)).X₃) ⟶
            freeMod 𝔸 ((T.map (indOf : C ⥤ Ind C)).X₂),
          s ≫ freeModMap 𝔸 ((T.map (indOf : C ⥤ Ind C)).g) =
            𝟙 (freeMod 𝔸 ((T.map (indOf : C ⥤ Ind C)).X₃))) := by
  letI := linearOfScalarUnit ψ
  letI := monoidalLinearOfScalarUnitBraided ψ
  letI := linearOfScalarUnit (indScalarUnit ψ)
  letI := monoidalLinearOfScalarUnitBraided (indScalarUnit ψ)
  classical
  have hu : HasScalarUnit C := hasScalarUnit_of_scalarUnit ψ
  have h1 : ¬ IsZero (𝟙_ (Ind C)) := not_isZero_unit_ind hu
  obtain ⟨𝔸, hmon, hcomm, hne, hmixed, hsec⟩ :=
    exists_splitting_algebra (C := C) hu L
      (K := { T : ShortComplex C // T.ShortExact })
      (fun k => (k.1.map (indOf : C ⥤ Ind C)).X₂)
      (fun k => (k.1.map (indOf : C ⥤ Ind C)).X₃)
      (fun k => (k.1.map (indOf : C ⥤ Ind C)).g)
      (fun Z => by
        obtain ⟨lam, hk⟩ := hkill Z
        exact locallyMixed_indOf ψ P P₀ Z lam hk L h1)
      (fun k => rappel210_indOf k.1 k.2 h1)
  refine ⟨𝔸, hmon, hcomm, hne, hmixed, fun T hT => ?_⟩
  exact hsec ⟨T, hT⟩

end RS
