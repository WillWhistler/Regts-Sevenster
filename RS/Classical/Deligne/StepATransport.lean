import RS.Classical.Deligne.BaseChangeDatum
import RS.Classical.Deligne.BaseChangeFree
import RS.Classical.Deligne.MixShuffle

/-!
# Transport of the dévissage decomposition

The decomposition of a state is carried along a base change and
recombined with the splitting of the remainder: one further unit
summand joins the mixed free part.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  [SymmetricCategory D]
variable [Preadditive D] [MonoidalPreadditive D]
  [HasFiniteBiproducts D] [HasCoequalizers D]
variable [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair
  (tensorLeft Z)]
variable [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair
  (tensorRight Z)]
variable (A : D) [MonObj A] [IsCommMonObj A]
variable (B : D) [MonObj B] [IsCommMonObj B]
variable (φ : A ⟶ B) [IsMonHom φ]

attribute [local instance]
  hasBinaryBiproducts_of_finite_biproducts

/-- **Base change on morphisms of modules.** -/
noncomputable def baseChangeMapMod {P Q : Mod D A}
    (g : P ⟶ Q) : baseChangeMod φ P ⟶ baseChangeMod φ Q :=
  Mod.Hom.mk' (modTensorMap A (𝟙 (restrictRegular φ)) g) (by
    exact baseChangeAct_modTensorMap A B φ g)

omit [Preadditive D] [MonoidalPreadditive D]
  [HasFiniteBiproducts D]
  [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair
    (tensorRight Z)] [IsCommMonObj A] in
@[simp] lemma baseChangeMapMod_hom {P Q : Mod D A}
    (g : P ⟶ Q) :
    (baseChangeMapMod A B φ g).hom =
      modTensorMap A (𝟙 (restrictRegular φ)) g := rfl

/-- **Base change is functorial on isomorphisms.** -/
noncomputable def baseChangeMapIso {P Q : Mod D A} (e : P ≅ Q) :
    baseChangeMod φ P ≅ baseChangeMod φ Q where
  hom := Mod.Hom.mk'
    (modTensorMap A (𝟙 (restrictRegular φ)) e.hom) (by
      exact baseChangeAct_modTensorMap A B φ e.hom)
  inv := Mod.Hom.mk'
    (modTensorMap A (𝟙 (restrictRegular φ)) e.inv) (by
      exact baseChangeAct_modTensorMap A B φ e.inv)
  hom_inv_id := by
    apply Mod.Hom.ext
    show modTensorMap A (𝟙 (restrictRegular φ)) e.hom ≫
      modTensorMap A (𝟙 (restrictRegular φ)) e.inv =
      𝟙 (modTensor A (restrictRegular φ) P)
    rw [← modTensorMap_comp, Category.comp_id, e.hom_inv_id,
      modTensorMap_id]
  inv_hom_id := by
    apply Mod.Hom.ext
    show modTensorMap A (𝟙 (restrictRegular φ)) e.inv ≫
      modTensorMap A (𝟙 (restrictRegular φ)) e.hom =
      𝟙 (modTensor A (restrictRegular φ) Q)
    rw [← modTensorMap_comp, Category.comp_id, e.inv_hom_id,
      modTensorMap_id]

section Mixed

variable (L : OddLine D) (r s : ℕ)

/-- **The mixed free part absorbs a unit summand.** -/
noncomputable def freeMixSuccIso :
    modBiprod B (regularMod B) (freeMod B (L.mix r s)) ≅
      freeMod B (L.mix (r + 1) s) :=
  (modBiprodMapIso B _ _ (freeModUnitIso B).symm
    (Iso.refl (freeMod B (L.mix r s)))).trans
    ((freeModBiprodIso B (𝟙_ D) (L.mix r s)).symm.trans
      (freeModMapIso B (L.mixSuccIso r s).symm))

/-- **The transported decomposition**: a state decomposition,
base-changed and recombined with a splitting of the remainder,
gains one unit summand in the mixed free part. -/
noncomputable def transportDecomp {X : D} {R : Mod D A}
    (e : freeMod A X ≅ modBiprod A (freeMod A (L.mix r s)) R)
    {R'' : Mod D B}
    (f : baseChangeMod φ R ≅
      modBiprod B (regularMod B) R'') :
    freeMod B X ≅
      modBiprod B (freeMod B (L.mix (r + 1) s)) R'' :=
  (baseChangeFreeIso A B φ X).symm.trans
    ((baseChangeMapIso A B φ e).trans
      ((baseChangeBiprodIso A B φ (freeMod A (L.mix r s)) R
        ).trans
        ((modBiprodMapIso B _ _
          (baseChangeFreeIso A B φ (L.mix r s)) f).trans
          ((modBiprodAssocIso B (freeMod B (L.mix r s))
            (regularMod B) R'').symm.trans
            (modBiprodMapIso B _ _
              ((modBiprodSymmIso B (freeMod B (L.mix r s))
                (regularMod B)).trans
                (freeMixSuccIso B L r s))
              (Iso.refl R''))))))

end Mixed

end RS
