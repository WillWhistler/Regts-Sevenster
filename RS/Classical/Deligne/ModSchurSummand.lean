import RS.Classical.Deligne.ModSchur
import RS.Classical.Deligne.ModBiprod

/-!
# Module-level Schur vanishing passes to retracts

A retract of a module inherits the vanishing of a block's action
on the relative tensor powers: the module-power map of the section
is a split monomorphism and intertwines the two actions.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  [SymmetricCategory D]
variable [Preadditive D] [MonoidalPreadditive D]
  [HasFiniteBiproducts D] [HasCoequalizers D]
variable [Linear ℂ D] [MonoidalLinear ℂ D]
variable [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair
  (tensorLeft Y)]
variable (A : D) [MonObj A]

omit [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair
    (tensorLeft Y)] in
/-- **Module-level Schur vanishing passes to retracts.** -/
theorem ModSchurKilled.of_split {X Y : D} [ModObj A X] [ModObj A Y]
    (s : X ⟶ Y) [IsModHom A s] (r : Y ⟶ X) [IsModHom A r]
    (hsr : s ≫ r = 𝟙 X) (P : SchurPackage.{v})
    {lam : YoungDiagram} (h : ModSchurKilled A Y P lam) :
    ModSchurKilled A X P lam := by
  have hmap : modPowMap A s lam.card ≫ modPowMap A r lam.card =
      𝟙 (modPow A X lam.card) := by
    apply modPow_hom_ext A X
    rw [modPowπ_map_assoc, modPowπ_map, Category.comp_id,
      ← Category.assoc, ← tensorPowMap_comp, hsr, tensorPowMap_id,
      Category.id_comp]
  have key : (modPowAlg A X lam.card (P.e lam) :
      modPow A X lam.card ⟶ modPow A X lam.card) ≫
      modPowMap A s lam.card = 0 := by
    rw [← modPowMap_alg A s lam.card (P.e lam), h]
    exact Limits.comp_zero
  have hpost := congrArg
    (fun t => t ≫ modPowMap A r lam.card) key
  simp only [Category.assoc, hmap, Category.comp_id,
    Limits.zero_comp] at hpost
  exact hpost

attribute [local instance]
  hasBinaryBiproducts_of_finite_biproducts

omit [MonoidalLinear ℂ D]
  [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair
    (tensorLeft Y)] in
/-- **Module-level Schur vanishing passes to the first biproduct
summand.** -/
theorem ModSchurKilled.of_biprod_left (M N : Mod D A)
    (P : SchurPackage.{v}) {lam : YoungDiagram}
    (h : ModSchurKilled A (modBiprod A M N).X P lam) :
    ModSchurKilled A M.X P lam := by
  haveI := (modBiprodInl A M N).isModHom
  haveI := (modBiprodFst A M N).isModHom
  refine ModSchurKilled.of_split A (modBiprodInl A M N).hom
    (modBiprodFst A M N).hom ?_ P h
  show (biprod.inl : M.X ⟶ M.X ⊞ N.X) ≫ biprod.fst = 𝟙 M.X
  exact biprod.inl_fst

omit [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair
    (tensorLeft Y)] in
/-- **Module-level Schur vanishing is invariant under
isomorphism.** -/
theorem ModSchurKilled.of_modIso {M N : Mod D A} (e : M ≅ N)
    (P : SchurPackage.{v}) {lam : YoungDiagram}
    (h : ModSchurKilled A N.X P lam) :
    ModSchurKilled A M.X P lam := by
  haveI := e.hom.isModHom
  haveI := e.inv.isModHom
  refine ModSchurKilled.of_split A e.hom.hom e.inv.hom ?_ P h
  have h1 := congrArg Mod.Hom.hom e.hom_inv_id
  rw [Mod.comp_hom', Mod.id_hom'] at h1
  exact h1

end RS
