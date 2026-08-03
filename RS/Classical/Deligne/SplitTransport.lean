import RS.Classical.Deligne.MixedTransport
import RS.Classical.Deligne.BaseChangeTransport

/-!
# Transport of a splitting along a base change

The base-change comparison of free modules is natural in the
object, so a section of a free morphism over one algebra
base-changes to a section over any algebra under it.
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

omit [Preadditive D] [MonoidalPreadditive D]
  [HasFiniteBiproducts D]
  [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair
    (tensorRight Z)] [IsCommMonObj A] in
/-- **The base-change comparison is natural**, at the carrier. -/
theorem baseChangeFreeInv_natural {V W : D} (f : V ⟶ W) :
    (B ◁ f) ≫ baseChangeFreeInv A B φ W =
      baseChangeFreeInv A B φ V ≫
        (baseChangeMapMod A B φ (freeModMap A f)).hom := by
  have hcore : f ≫ ((λ_ W).inv ≫ (η[A] ▷ W)) =
      ((λ_ V).inv ≫ (η[A] ▷ V)) ≫ (A ◁ f) := by
    rw [leftUnitor_inv_naturality_assoc, whisker_exchange,
      Category.assoc]
  have hmap : modTensorπ A (restrictRegular φ) (freeMod A V) ≫
      modTensorMap A (𝟙 (restrictRegular φ)) (freeModMap A f) =
      (B ◁ (A ◁ f)) ≫
        modTensorπ A (restrictRegular φ) (freeMod A W) := by
    refine Eq.trans (modTensorπ_map A _ _) ?_
    rw [Mod.id_hom', MonoidalCategory.id_tensorHom]
    rfl
  rw [baseChangeMapMod_hom, baseChangeFreeInv, baseChangeFreeInv]
  refine Eq.trans ?_ (Eq.trans (Category.assoc _ _ _)
    (whisker_eq _ hmap)).symm
  rw [← MonoidalCategory.whiskerLeft_comp_assoc, hcore,
    MonoidalCategory.whiskerLeft_comp_assoc]
  rfl

omit [Preadditive D] [MonoidalPreadditive D]
  [HasFiniteBiproducts D]
  [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair
    (tensorRight Z)] [IsCommMonObj A] in
/-- **The base-change comparison is natural**, as module maps. -/
theorem baseChangeFreeIso_inv_natural {V W : D} (f : V ⟶ W) :
    freeModMap B f ≫ (baseChangeFreeIso A B φ W).inv =
      (baseChangeFreeIso A B φ V).inv ≫
        baseChangeMapMod A B φ (freeModMap A f) := by
  apply Mod.Hom.ext
  rw [Mod.comp_hom', Mod.comp_hom']
  show (B ◁ f) ≫ baseChangeFreeInv A B φ W =
    baseChangeFreeInv A B φ V ≫
      (baseChangeMapMod A B φ (freeModMap A f)).hom
  exact baseChangeFreeInv_natural A B φ f

omit [Preadditive D] [MonoidalPreadditive D]
  [HasFiniteBiproducts D]
  [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair
    (tensorRight Z)] [IsCommMonObj A] in
/-- **A section of a free morphism base-changes.** -/
theorem exists_section_baseChange (ψ : A ⟶ B) [IsMonHom ψ]
    {V W : D} (g : V ⟶ W)
    (s : freeMod A W ⟶ freeMod A V)
    (hs : s ≫ freeModMap A g = 𝟙 (freeMod A W)) :
    ∃ t : freeMod B W ⟶ freeMod B V,
      t ≫ freeModMap B g = 𝟙 (freeMod B W) := by
  refine ⟨(baseChangeFreeIso A B ψ W).inv ≫
    baseChangeMapMod A B ψ s ≫
    (baseChangeFreeIso A B ψ V).hom, ?_⟩
  have hnat := baseChangeFreeIso_inv_natural A B ψ g
  have hkey : (baseChangeFreeIso A B ψ V).hom ≫ freeModMap B g =
      baseChangeMapMod A B ψ (freeModMap A g) ≫
        (baseChangeFreeIso A B ψ W).hom := by
    rw [← Iso.eq_inv_comp, ← Category.assoc, ← hnat,
      Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [Category.assoc, Category.assoc, hkey, ← Category.assoc
    (baseChangeMapMod A B ψ s), ← baseChangeMapMod_comp, hs,
    baseChangeMapMod_id, Category.id_comp]
  simp

end RS
