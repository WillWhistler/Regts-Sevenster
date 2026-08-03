import RS.Classical.Deligne.SplitExtract
import RS.Classical.Deligne.ModBiprod

/-!
# The complement of the split factor

The evaluation followed by the coevaluation is a linear
idempotent on the base change of the module; its kernel is the
complement of the split unit factor, and carries the descended
action.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  [SymmetricCategory D]
variable [Preadditive D] [MonoidalPreadditive D]
  [HasCoequalizers D]
variable (A : D) [MonObj A] [IsCommMonObj A]
variable {M M' : Mod D A}
variable (B : D) [MonObj B] [IsCommMonObj B]
variable (φ : A ⟶ B) [IsMonHom φ]
variable [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair
  (tensorLeft Z)]
variable (v : M.X ⟶ B) (w : M'.X ⟶ B)
variable (d : ModDualityDatum A M M')

/-- **The split idempotent** on the base change: evaluate, then
coevaluate. -/
noncomputable def splitIdem
    (hv : actLeft A M.X ≫ v =
      (A ◁ v) ≫ (φ ▷ B) ≫ μ[B])
    (hw : actLeft A M'.X ≫ w =
      (A ◁ w) ≫ (φ ▷ B) ≫ μ[B]) :
    baseChange φ M ⟶ baseChange φ M :=
  splitEval A B φ v hv ≫ splitCoeval A B φ w d hw

omit [Preadditive D] [MonoidalPreadditive D] in
/-- The split idempotent is idempotent. -/
theorem splitIdem_idem
    (hv : actLeft A M.X ≫ v =
      (A ◁ v) ≫ (φ ▷ B) ≫ μ[B])
    (hw : actLeft A M'.X ≫ w =
      (A ◁ w) ≫ (φ ▷ B) ≫ μ[B])
    (p : modTensor A M M' ⟶ B)
    (hp : modTensorπ A M M' ≫ p = (v ⊗ₘ w) ≫ μ[B])
    (hδ : η[A] ≫ d.copair ≫ p = η[B]) :
    splitIdem A B φ v w d hv hw ≫
        splitIdem A B φ v w d hv hw =
      splitIdem A B φ v w d hv hw := by
  rw [splitIdem, Category.assoc,
    ← Category.assoc (splitCoeval A B φ w d hw),
    splitCoeval_splitEval A B φ v w d hv hw p hp hδ,
    Category.id_comp]

omit [Preadditive D] [MonoidalPreadditive D] in
/-- The split idempotent is linear over the algebra. -/
theorem baseChangeAct_splitIdem
    (hv : actLeft A M.X ≫ v =
      (A ◁ v) ≫ (φ ▷ B) ≫ μ[B])
    (hw : actLeft A M'.X ≫ w =
      (A ◁ w) ≫ (φ ▷ B) ≫ μ[B]) :
    baseChangeAct φ M ≫ splitIdem A B φ v w d hv hw =
      (B ◁ splitIdem A B φ v w d hv hw) ≫
        baseChangeAct φ M := by
  rw [splitIdem, ← Category.assoc,
    baseChangeAct_splitEval A B φ v hv, Category.assoc,
    mul_splitCoeval A B φ w d hw,
    MonoidalCategory.whiskerLeft_comp]
  simp only [Category.assoc]

section Complement

variable [HasKernels D]

/-- **The complement carrier**: the kernel of the split
idempotent. -/
noncomputable def splitCompl
    (hv : actLeft A M.X ≫ v =
      (A ◁ v) ≫ (φ ▷ B) ≫ μ[B])
    (hw : actLeft A M'.X ≫ w =
      (A ◁ w) ≫ (φ ▷ B) ≫ μ[B]) : D :=
  kernel (splitIdem A B φ v w d hv hw)

/-- The action of the algebra descends to the complement. -/
noncomputable def splitComplAct
    (hv : actLeft A M.X ≫ v =
      (A ◁ v) ≫ (φ ▷ B) ≫ μ[B])
    (hw : actLeft A M'.X ≫ w =
      (A ◁ w) ≫ (φ ▷ B) ≫ μ[B]) :
    B ⊗ splitCompl A B φ v w d hv hw ⟶
      splitCompl A B φ v w d hv hw :=
  kernel.lift _
    ((B ◁ kernel.ι (splitIdem A B φ v w d hv hw)) ≫
      baseChangeAct φ M) (by
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (whisker_eq _
      (baseChangeAct_splitIdem A B φ v w d hv hw)) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (eq_whisker
      (MonoidalCategory.whiskerLeft_comp B _ _).symm _) ?_
    refine Eq.trans (eq_whisker (congrArg (fun t => B ◁ t)
      (kernel.condition
        (splitIdem A B φ v w d hv hw))) _) ?_
    rw [MonoidalPreadditive.whiskerLeft_zero,
      Limits.zero_comp]
    rfl)


/-- Defining equation of the complement action. -/
@[reassoc]
theorem splitComplAct_ι
    (hv : actLeft A M.X ≫ v =
      (A ◁ v) ≫ (φ ▷ B) ≫ μ[B])
    (hw : actLeft A M'.X ≫ w =
      (A ◁ w) ≫ (φ ▷ B) ≫ μ[B]) :
    splitComplAct A B φ v w d hv hw ≫
        kernel.ι (splitIdem A B φ v w d hv hw) =
      (B ◁ kernel.ι (splitIdem A B φ v w d hv hw)) ≫
        baseChangeAct φ M :=
  kernel.lift_ι _ _ _

/-- The unit law of the complement action. -/
theorem splitComplAct_one
    (hv : actLeft A M.X ≫ v =
      (A ◁ v) ≫ (φ ▷ B) ≫ μ[B])
    (hw : actLeft A M'.X ≫ w =
      (A ◁ w) ≫ (φ ▷ B) ≫ μ[B]) :
    (η[B] ▷ splitCompl A B φ v w d hv hw) ≫
        splitComplAct A B φ v w d hv hw =
      (λ_ (splitCompl A B φ v w d hv hw)).hom := by
  letI := baseChangeModObj φ M
  have hι : ((η[B] ▷ splitCompl A B φ v w d hv hw) ≫
      splitComplAct A B φ v w d hv hw) ≫
      kernel.ι (splitIdem A B φ v w d hv hw) =
      (λ_ (splitCompl A B φ v w d hv hw)).hom ≫
        kernel.ι (splitIdem A B φ v w d hv hw) := by
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (whisker_eq _
      (splitComplAct_ι A B φ v w d hv hw)) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (eq_whisker
      (whisker_exchange η[B] (kernel.ι
        (splitIdem A B φ v w d hv hw))).symm _) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (whisker_eq _
      (one_actLeft B (baseChange φ M))) ?_
    exact leftUnitor_naturality _
  exact (cancel_mono
    (kernel.ι (splitIdem A B φ v w d hv hw))).mp hι

/-- The multiplication law of the complement action. -/
theorem splitComplAct_mul
    (hv : actLeft A M.X ≫ v =
      (A ◁ v) ≫ (φ ▷ B) ≫ μ[B])
    (hw : actLeft A M'.X ≫ w =
      (A ◁ w) ≫ (φ ▷ B) ≫ μ[B]) :
    (μ[B] ▷ splitCompl A B φ v w d hv hw) ≫
        splitComplAct A B φ v w d hv hw =
      (α_ B B (splitCompl A B φ v w d hv hw)).hom ≫
        (B ◁ splitComplAct A B φ v w d hv hw) ≫
        splitComplAct A B φ v w d hv hw := by
  letI := baseChangeModObj φ M
  have hι : ((μ[B] ▷ splitCompl A B φ v w d hv hw) ≫
      splitComplAct A B φ v w d hv hw) ≫
      kernel.ι (splitIdem A B φ v w d hv hw) =
      ((α_ B B (splitCompl A B φ v w d hv hw)).hom ≫
        (B ◁ splitComplAct A B φ v w d hv hw) ≫
        splitComplAct A B φ v w d hv hw) ≫
      kernel.ι (splitIdem A B φ v w d hv hw) := by
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (whisker_eq _
      (splitComplAct_ι A B φ v w d hv hw)) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (eq_whisker
      (whisker_exchange μ[B] (kernel.ι
        (splitIdem A B φ v w d hv hw))).symm _) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (whisker_eq _
      (mul_actLeft B (baseChange φ M))) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (eq_whisker
      (associator_naturality_right B B (kernel.ι
        (splitIdem A B φ v w d hv hw))) _) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.symm ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine whisker_eq _ ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (whisker_eq _
      (splitComplAct_ι A B φ v w d hv hw)) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (eq_whisker
      (MonoidalCategory.whiskerLeft_comp B _ _).symm _) ?_
    refine Eq.trans (eq_whisker (congrArg (fun t => B ◁ t)
      (splitComplAct_ι A B φ v w d hv hw)) _) ?_
    refine Eq.trans (eq_whisker
      (MonoidalCategory.whiskerLeft_comp B _ _) _) ?_
    exact Category.assoc _ _ _
  exact (cancel_mono
    (kernel.ι (splitIdem A B φ v w d hv hw))).mp hι

/-- The complement, as a module over the algebra. -/
@[implicit_reducible]
noncomputable def splitComplModObj
    (hv : actLeft A M.X ≫ v =
      (A ◁ v) ≫ (φ ▷ B) ≫ μ[B])
    (hw : actLeft A M'.X ≫ w =
      (A ◁ w) ≫ (φ ▷ B) ≫ μ[B]) :
    ModObj B (splitCompl A B φ v w d hv hw) where
  smul := splitComplAct A B φ v w d hv hw
  one_smul := splitComplAct_one A B φ v w d hv hw
  mul_smul := splitComplAct_mul A B φ v w d hv hw

/-- The complement, bundled. -/
noncomputable def splitComplMod
    (hv : actLeft A M.X ≫ v =
      (A ◁ v) ≫ (φ ▷ B) ≫ μ[B])
    (hw : actLeft A M'.X ≫ w =
      (A ◁ w) ≫ (φ ▷ B) ≫ μ[B]) : Mod D B :=
  letI := splitComplModObj A B φ v w d hv hw
  ⟨splitCompl A B φ v w d hv hw⟩

/-- The projection onto the complement: the complementary
idempotent, corestricted to the kernel. -/
noncomputable def splitComplProj
    (hv : actLeft A M.X ≫ v =
      (A ◁ v) ≫ (φ ▷ B) ≫ μ[B])
    (hw : actLeft A M'.X ≫ w =
      (A ◁ w) ≫ (φ ▷ B) ≫ μ[B])
    (p : modTensor A M M' ⟶ B)
    (hp : modTensorπ A M M' ≫ p = (v ⊗ₘ w) ≫ μ[B])
    (hδ : η[A] ≫ d.copair ≫ p = η[B]) :
    baseChange φ M ⟶ splitCompl A B φ v w d hv hw :=
  kernel.lift _ (𝟙 (baseChange φ M) -
    splitIdem A B φ v w d hv hw) (by
    rw [Preadditive.sub_comp, Category.id_comp,
      splitIdem_idem A B φ v w d hv hw p hp hδ, sub_self])

omit [MonoidalPreadditive D] in
/-- Defining equation of the projection. -/
@[reassoc]
theorem splitComplProj_ι
    (hv : actLeft A M.X ≫ v =
      (A ◁ v) ≫ (φ ▷ B) ≫ μ[B])
    (hw : actLeft A M'.X ≫ w =
      (A ◁ w) ≫ (φ ▷ B) ≫ μ[B])
    (p : modTensor A M M' ⟶ B)
    (hp : modTensorπ A M M' ≫ p = (v ⊗ₘ w) ≫ μ[B])
    (hδ : η[A] ≫ d.copair ≫ p = η[B]) :
    splitComplProj A B φ v w d hv hw p hp hδ ≫
        kernel.ι (splitIdem A B φ v w d hv hw) =
      𝟙 (baseChange φ M) - splitIdem A B φ v w d hv hw :=
  kernel.lift_ι _ _ _

variable [HasBinaryBiproducts D]

/-- **The decomposition of the base change**, carrier level: the
algebra summand against the complement. -/
noncomputable def splitDecomp
    (hv : actLeft A M.X ≫ v =
      (A ◁ v) ≫ (φ ▷ B) ≫ μ[B])
    (hw : actLeft A M'.X ≫ w =
      (A ◁ w) ≫ (φ ▷ B) ≫ μ[B])
    (p : modTensor A M M' ⟶ B)
    (hp : modTensorπ A M M' ≫ p = (v ⊗ₘ w) ≫ μ[B])
    (hδ : η[A] ≫ d.copair ≫ p = η[B]) :
    baseChange φ M ≅ B ⊞ splitCompl A B φ v w d hv hw where
  hom := biprod.lift (splitEval A B φ v hv)
    (splitComplProj A B φ v w d hv hw p hp hδ)
  inv := biprod.desc (splitCoeval A B φ w d hw)
    (kernel.ι (splitIdem A B φ v w d hv hw))
  hom_inv_id := by
    rw [biprod.lift_desc,
      splitComplProj_ι A B φ v w d hv hw p hp hδ]
    rw [show splitEval A B φ v hv ≫
      splitCoeval A B φ w d hw =
        splitIdem A B φ v w d hv hw from rfl]
    rw [add_sub_cancel]
  inv_hom_id := by
    apply biprod.hom_ext'
    · rw [biprod.inl_desc_assoc, Category.comp_id]
      apply biprod.hom_ext
      · rw [Category.assoc, biprod.lift_fst, biprod.inl_fst,
          splitCoeval_splitEval A B φ v w d hv hw p hp hδ]
      · rw [Category.assoc, biprod.lift_snd, biprod.inl_snd]
        refine (cancel_mono (kernel.ι
          (splitIdem A B φ v w d hv hw))).mp ?_
        refine Eq.trans (Category.assoc _ _ _) ?_
        refine Eq.trans (whisker_eq _
          (splitComplProj_ι A B φ v w d hv hw p hp hδ)) ?_
        rw [Preadditive.comp_sub, Category.comp_id]
        refine Eq.trans ?_ (Limits.zero_comp (f := kernel.ι
          (splitIdem A B φ v w d hv hw))).symm
        rw [show splitCoeval A B φ w d hw ≫
          splitIdem A B φ v w d hv hw =
            (splitCoeval A B φ w d hw ≫
              splitEval A B φ v hv) ≫
              splitCoeval A B φ w d hw from
          (Category.assoc _ _ _).symm]
        rw [splitCoeval_splitEval A B φ v w d hv hw p hp hδ,
          Category.id_comp, sub_self]
    · rw [biprod.inr_desc_assoc, Category.comp_id]
      apply biprod.hom_ext
      · rw [Category.assoc, biprod.lift_fst, biprod.inr_fst]
        haveI : IsSplitMono (splitCoeval A B φ w d hw) :=
          IsSplitMono.mk' ⟨splitEval A B φ v hv,
            splitCoeval_splitEval A B φ v w d hv hw p hp hδ⟩
        refine (cancel_mono
          (splitCoeval A B φ w d hw)).mp ?_
        rw [Limits.zero_comp, Category.assoc]
        exact kernel.condition _
      · rw [Category.assoc, biprod.lift_snd, biprod.inr_snd]
        refine (cancel_mono (kernel.ι
          (splitIdem A B φ v w d hv hw))).mp ?_
        refine Eq.trans (Category.assoc _ _ _) ?_
        refine Eq.trans (whisker_eq _
          (splitComplProj_ι A B φ v w d hv hw p hp hδ)) ?_
        rw [Preadditive.comp_sub, Category.comp_id]
        have h1 : kernel.ι (splitIdem A B φ v w d hv hw) ≫
            splitIdem A B φ v w d hv hw = 0 :=
          kernel.condition _
        refine Eq.trans (congrArg (fun t =>
          kernel.ι (splitIdem A B φ v w d hv hw) - t) h1) ?_
        refine Eq.trans (sub_zero _) ?_
        exact (Category.id_comp _).symm

omit [HasBinaryBiproducts D] in
/-- The projection is linear over the algebra. -/
@[reassoc]
theorem baseChangeAct_splitComplProj
    (hv : actLeft A M.X ≫ v =
      (A ◁ v) ≫ (φ ▷ B) ≫ μ[B])
    (hw : actLeft A M'.X ≫ w =
      (A ◁ w) ≫ (φ ▷ B) ≫ μ[B])
    (p : modTensor A M M' ⟶ B)
    (hp : modTensorπ A M M' ≫ p = (v ⊗ₘ w) ≫ μ[B])
    (hδ : η[A] ≫ d.copair ≫ p = η[B]) :
    baseChangeAct φ M ≫
        splitComplProj A B φ v w d hv hw p hp hδ =
      (B ◁ splitComplProj A B φ v w d hv hw p hp hδ) ≫
        splitComplAct A B φ v w d hv hw := by
  refine (cancel_mono (kernel.ι
    (splitIdem A B φ v w d hv hw))).mp ?_
  have hL : (baseChangeAct φ M ≫
      splitComplProj A B φ v w d hv hw p hp hδ) ≫
      kernel.ι (splitIdem A B φ v w d hv hw) =
      baseChangeAct φ M -
        (B ◁ splitIdem A B φ v w d hv hw) ≫
          baseChangeAct φ M := by
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (whisker_eq _
      (splitComplProj_ι A B φ v w d hv hw p hp hδ)) ?_
    rw [Preadditive.comp_sub, Category.comp_id,
      baseChangeAct_splitIdem A B φ v w d hv hw]
  have hR : ((B ◁ splitComplProj A B φ v w d hv hw p hp hδ) ≫
      splitComplAct A B φ v w d hv hw) ≫
      kernel.ι (splitIdem A B φ v w d hv hw) =
      baseChangeAct φ M -
        (B ◁ splitIdem A B φ v w d hv hw) ≫
          baseChangeAct φ M := by
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (whisker_eq _
      (splitComplAct_ι A B φ v w d hv hw)) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (eq_whisker
      (MonoidalCategory.whiskerLeft_comp B _ _).symm _) ?_
    refine Eq.trans (eq_whisker (congrArg (fun t => B ◁ t)
      (splitComplProj_ι A B φ v w d hv hw p hp hδ)) _) ?_
    rw [show B ◁ (𝟙 (baseChange φ M) -
        splitIdem A B φ v w d hv hw) =
      B ◁ 𝟙 (baseChange φ M) -
        B ◁ splitIdem A B φ v w d hv hw from
      Functor.map_sub (F := tensorLeft B)]
    rw [Preadditive.sub_comp,
      MonoidalCategory.whiskerLeft_id, Category.id_comp]
  exact hL.trans hR.symm

omit [SymmetricCategory D] [HasCoequalizers D]
  [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair
    (tensorLeft Z)] [HasKernels D] in
/-- Morphisms out of a tensored biproduct are determined by the
two whiskered injections. -/
private theorem whisker_biprod_ext {P X Y Z : D}
    {f g : P ⊗ (X ⊞ Y) ⟶ Z}
    (h1 : (P ◁ biprod.inl) ≫ f = (P ◁ biprod.inl) ≫ g)
    (h2 : (P ◁ biprod.inr) ≫ f = (P ◁ biprod.inr) ≫ g) :
    f = g := by
  have htot : 𝟙 (P ⊗ (X ⊞ Y)) =
      (P ◁ biprod.fst) ≫ (P ◁ biprod.inl) +
      (P ◁ biprod.snd) ≫ (P ◁ biprod.inr) := by
    rw [← MonoidalCategory.whiskerLeft_comp,
      ← MonoidalCategory.whiskerLeft_comp,
      ← MonoidalPreadditive.whiskerLeft_add, biprod.total,
      MonoidalCategory.whiskerLeft_id]
  calc f = 𝟙 (P ⊗ (X ⊞ Y)) ≫ f := (Category.id_comp f).symm
    _ = ((P ◁ biprod.fst) ≫ (P ◁ biprod.inl) +
        (P ◁ biprod.snd) ≫ (P ◁ biprod.inr)) ≫ f := by
        rw [← htot]
    _ = (P ◁ biprod.fst) ≫ ((P ◁ biprod.inl) ≫ g) +
        (P ◁ biprod.snd) ≫ ((P ◁ biprod.inr) ≫ g) := by
        rw [Preadditive.add_comp]
        simp only [Category.assoc]
        rw [h1, h2]
    _ = ((P ◁ biprod.fst) ≫ (P ◁ biprod.inl) +
        (P ◁ biprod.snd) ≫ (P ◁ biprod.inr)) ≫ g := by
        rw [Preadditive.add_comp]
        simp only [Category.assoc]
    _ = 𝟙 (P ⊗ (X ⊞ Y)) ≫ g := by rw [← htot]
    _ = g := Category.id_comp g

/-- The decomposition intertwines the actions, forward
direction. -/
theorem baseChangeAct_splitDecompHom
    (hv : actLeft A M.X ≫ v =
      (A ◁ v) ≫ (φ ▷ B) ≫ μ[B])
    (hw : actLeft A M'.X ≫ w =
      (A ◁ w) ≫ (φ ▷ B) ≫ μ[B])
    (p : modTensor A M M' ⟶ B)
    (hp : modTensorπ A M M' ≫ p = (v ⊗ₘ w) ≫ μ[B])
    (hδ : η[A] ≫ d.copair ≫ p = η[B]) :
    baseChangeAct φ M ≫
      biprod.lift (splitEval A B φ v hv)
        (splitComplProj A B φ v w d hv hw p hp hδ) =
    (B ◁ biprod.lift (splitEval A B φ v hv)
        (splitComplProj A B φ v w d hv hw p hp hδ)) ≫
      modBiprodAct B (regularMod B)
        (splitComplMod A B φ v w d hv hw) := by
  apply biprod.hom_ext
  · refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (whisker_eq _ (biprod.lift_fst _ _)) ?_
    refine Eq.symm ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (whisker_eq _
      (modBiprodAct_fst B (regularMod B)
        (splitComplMod A B φ v w d hv hw))) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (eq_whisker
      (MonoidalCategory.whiskerLeft_comp B _ _).symm _) ?_
    refine Eq.trans (eq_whisker (congrArg (fun t => B ◁ t)
      (biprod.lift_fst (splitEval A B φ v hv)
        (splitComplProj A B φ v w d hv hw p hp hδ))) _) ?_
    exact (baseChangeAct_splitEval A B φ v hv).symm
  · refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (whisker_eq _ (biprod.lift_snd _ _)) ?_
    refine Eq.symm ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (whisker_eq _
      (modBiprodAct_snd B (regularMod B)
        (splitComplMod A B φ v w d hv hw))) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (eq_whisker
      (MonoidalCategory.whiskerLeft_comp B _ _).symm _) ?_
    refine Eq.trans (eq_whisker (congrArg (fun t => B ◁ t)
      (biprod.lift_snd (splitEval A B φ v hv)
        (splitComplProj A B φ v w d hv hw p hp hδ))) _) ?_
    exact
      (baseChangeAct_splitComplProj A B φ v w d hv hw
        p hp hδ).symm

/-- The decomposition intertwines the actions, inverse
direction. -/
theorem modBiprodAct_splitDecompInv
    (hv : actLeft A M.X ≫ v =
      (A ◁ v) ≫ (φ ▷ B) ≫ μ[B])
    (hw : actLeft A M'.X ≫ w =
      (A ◁ w) ≫ (φ ▷ B) ≫ μ[B]) :
    modBiprodAct B (regularMod B)
        (splitComplMod A B φ v w d hv hw) ≫
      biprod.desc (splitCoeval A B φ w d hw)
        (kernel.ι (splitIdem A B φ v w d hv hw)) =
    (B ◁ biprod.desc (splitCoeval A B φ w d hw)
        (kernel.ι (splitIdem A B φ v w d hv hw))) ≫
      baseChangeAct φ M := by
  apply whisker_biprod_ext
  · refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (eq_whisker
      (actLeft_modBiprodInl B (regularMod B)
        (splitComplMod A B φ v w d hv hw)).symm _) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (whisker_eq _ (biprod.inl_desc _ _)) ?_
    refine Eq.symm ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (eq_whisker
      (MonoidalCategory.whiskerLeft_comp B _ _).symm _) ?_
    refine Eq.trans (eq_whisker (congrArg (fun t => B ◁ t)
      (biprod.inl_desc (splitCoeval A B φ w d hw)
        (kernel.ι (splitIdem A B φ v w d hv hw)))) _) ?_
    exact (mul_splitCoeval A B φ w d hw).symm
  · refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (eq_whisker
      (actLeft_modBiprodInr B (regularMod B)
        (splitComplMod A B φ v w d hv hw)).symm _) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (whisker_eq _ (biprod.inr_desc _ _)) ?_
    refine Eq.symm ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (eq_whisker
      (MonoidalCategory.whiskerLeft_comp B _ _).symm _) ?_
    refine Eq.trans (eq_whisker (congrArg (fun t => B ◁ t)
      (biprod.inr_desc (splitCoeval A B φ w d hw)
        (kernel.ι (splitIdem A B φ v w d hv hw)))) _) ?_
    exact (splitComplAct_ι A B φ v w d hv hw).symm

/-- **The decomposition at the module level**: the base change
of the module is the regular module plus the complement, as
modules over the algebra. -/
noncomputable def splitDecompMod
    (hv : actLeft A M.X ≫ v =
      (A ◁ v) ≫ (φ ▷ B) ≫ μ[B])
    (hw : actLeft A M'.X ≫ w =
      (A ◁ w) ≫ (φ ▷ B) ≫ μ[B])
    (p : modTensor A M M' ⟶ B)
    (hp : modTensorπ A M M' ≫ p = (v ⊗ₘ w) ≫ μ[B])
    (hδ : η[A] ≫ d.copair ≫ p = η[B]) :
    baseChangeMod φ M ≅
      modBiprod B (regularMod B)
        (splitComplMod A B φ v w d hv hw) where
  hom := Mod.Hom.mk'
    (biprod.lift (splitEval A B φ v hv)
      (splitComplProj A B φ v w d hv hw p hp hδ))
    (by
      exact baseChangeAct_splitDecompHom A B φ v w d hv hw
        p hp hδ)
  inv := Mod.Hom.mk'
    (biprod.desc (splitCoeval A B φ w d hw)
      (kernel.ι (splitIdem A B φ v w d hv hw)))
    (by exact modBiprodAct_splitDecompInv A B φ v w d hv hw)
  hom_inv_id := by
    apply Mod.Hom.ext
    show biprod.lift (splitEval A B φ v hv)
        (splitComplProj A B φ v w d hv hw p hp hδ) ≫
      biprod.desc (splitCoeval A B φ w d hw)
        (kernel.ι (splitIdem A B φ v w d hv hw)) =
      𝟙 (baseChange φ M)
    exact (splitDecomp A B φ v w d hv hw p hp hδ).hom_inv_id
  inv_hom_id := by
    apply Mod.Hom.ext
    show biprod.desc (splitCoeval A B φ w d hw)
        (kernel.ι (splitIdem A B φ v w d hv hw)) ≫
      biprod.lift (splitEval A B φ v hv)
        (splitComplProj A B φ v w d hv hw p hp hδ) =
      𝟙 (B ⊞ splitCompl A B φ v w d hv hw)
    exact (splitDecomp A B φ v w d hv hw p hp hδ).inv_hom_id

end Complement

section Retract

variable [HasKernels D] [HasBinaryBiproducts D]

/-- The kernel inclusion of the complement, as a module map. -/
noncomputable def splitComplIncl
    (hv : actLeft A M.X ≫ v =
      (A ◁ v) ≫ (φ ▷ B) ≫ μ[B])
    (hw : actLeft A M'.X ≫ w =
      (A ◁ w) ≫ (φ ▷ B) ≫ μ[B]) :
    splitComplMod A B φ v w d hv hw ⟶ baseChangeMod φ M :=
  Mod.Hom.mk' (kernel.ι (splitIdem A B φ v w d hv hw)) (by
    exact splitComplAct_ι A B φ v w d hv hw)

/-- The projection onto the complement, as a module map. -/
noncomputable def splitComplProjMod
    (hv : actLeft A M.X ≫ v =
      (A ◁ v) ≫ (φ ▷ B) ≫ μ[B])
    (hw : actLeft A M'.X ≫ w =
      (A ◁ w) ≫ (φ ▷ B) ≫ μ[B])
    (p : modTensor A M M' ⟶ B)
    (hp : modTensorπ A M M' ≫ p = (v ⊗ₘ w) ≫ μ[B])
    (hδ : η[A] ≫ d.copair ≫ p = η[B]) :
    baseChangeMod φ M ⟶ splitComplMod A B φ v w d hv hw :=
  Mod.Hom.mk' (splitComplProj A B φ v w d hv hw p hp hδ) (by
    exact baseChangeAct_splitComplProj A B φ v w d hv hw
      p hp hδ)

omit [MonoidalPreadditive D] [HasBinaryBiproducts D] in
/-- **The complement is a retract of the base change**, at the
carrier. -/
theorem splitCompl_ι_proj
    (hv : actLeft A M.X ≫ v =
      (A ◁ v) ≫ (φ ▷ B) ≫ μ[B])
    (hw : actLeft A M'.X ≫ w =
      (A ◁ w) ≫ (φ ▷ B) ≫ μ[B])
    (p : modTensor A M M' ⟶ B)
    (hp : modTensorπ A M M' ≫ p = (v ⊗ₘ w) ≫ μ[B])
    (hδ : η[A] ≫ d.copair ≫ p = η[B]) :
    kernel.ι (splitIdem A B φ v w d hv hw) ≫
        splitComplProj A B φ v w d hv hw p hp hδ =
      𝟙 (splitCompl A B φ v w d hv hw) := by
  refine (cancel_mono
    (kernel.ι (splitIdem A B φ v w d hv hw))).mp ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (whisker_eq _
    (splitComplProj_ι A B φ v w d hv hw p hp hδ)) ?_
  rw [Preadditive.comp_sub, Category.comp_id]
  have h1 : kernel.ι (splitIdem A B φ v w d hv hw) ≫
      splitIdem A B φ v w d hv hw = 0 := kernel.condition _
  refine Eq.trans (congrArg (fun t =>
    kernel.ι (splitIdem A B φ v w d hv hw) - t) h1) ?_
  refine Eq.trans (sub_zero _) ?_
  exact (Category.id_comp _).symm

omit [HasBinaryBiproducts D] in
/-- **The complement is a retract of the base change**, as
modules. -/
theorem splitComplIncl_proj
    (hv : actLeft A M.X ≫ v =
      (A ◁ v) ≫ (φ ▷ B) ≫ μ[B])
    (hw : actLeft A M'.X ≫ w =
      (A ◁ w) ≫ (φ ▷ B) ≫ μ[B])
    (p : modTensor A M M' ⟶ B)
    (hp : modTensorπ A M M' ≫ p = (v ⊗ₘ w) ≫ μ[B])
    (hδ : η[A] ≫ d.copair ≫ p = η[B]) :
    splitComplIncl A B φ v w d hv hw ≫
        splitComplProjMod A B φ v w d hv hw p hp hδ =
      𝟙 (splitComplMod A B φ v w d hv hw) := by
  apply Mod.Hom.ext
  exact splitCompl_ι_proj A B φ v w d hv hw p hp hδ

end Retract

end RS
