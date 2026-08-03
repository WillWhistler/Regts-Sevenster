import RS.Classical.Deligne.PowCopairing

/-!
# Factor extraction from splitting data

The dévissage engine of the trichotomy: from splitting data over
a duality datum, the unit of the splitting algebra is a direct
factor of the base change of the module.  The insertion extends
`B`-linearly to an evaluation on the base change; the copairing
against the dual insertion supplies a coevaluation; the section
identity of the data makes the pair a retract.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  [SymmetricCategory D]
variable [HasCoequalizers D]
variable (A : D) [MonObj A] [IsCommMonObj A]
variable {M M' : Mod D A}
variable (B : D) [MonObj B] [IsCommMonObj B]
variable (φ : A ⟶ B) [IsMonHom φ]
variable [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair
  (tensorLeft Z)]

section Eval

variable (v : M.X ⟶ B)

omit [HasCoequalizers D] [IsCommMonObj A]
  [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair
    (tensorLeft Z)] in
/-- **The descent condition of the evaluation**: an insertion
that is linear over the base through `φ` coequalizes the two
legs of the base-change tensor. -/
theorem splitEvalCond (hv : actLeft A M.X ≫ v =
    (A ◁ v) ≫ (φ ▷ B) ≫ μ[B]) :
    modTensorLegM A (restrictRegular φ) M ≫
        (B ◁ v) ≫ μ[B] =
      modTensorLegN A (restrictRegular φ) M ≫
        (B ◁ v) ≫ μ[B] := by
  have h1 : modTensorLegM A (restrictRegular φ) M =
      (B ◁ φ ≫ μ[B]) ▷ M.X :=
    congrArg (· ▷ M.X) (actRight_restrictRegular φ)
  have h2 : modTensorLegN A (restrictRegular φ) M =
      (α_ B A M.X).hom ≫ (B ◁ actLeft A M.X) := rfl
  rw [h1, h2, Category.assoc,
    ← MonoidalCategory.whiskerLeft_comp_assoc, hv]
  simp only [MonoidalCategory.whiskerLeft_comp,
    Category.assoc, MonoidalCategory.comp_whiskerRight]
  rw [MonObj.mul_assoc_flip]
  simp only [← Category.assoc]
  congr 1
  simp only [Category.assoc]
  rw [← whisker_exchange]
  rw [← whisker_exchange_assoc]
  rw [← associator_naturality_right_assoc]
  rw [← associator_naturality_middle_assoc]
  simp

/-- **The evaluation of the insertion on the base change**: the
`B`-linear extension of a base-linear insertion. -/
noncomputable def splitEval (hv : actLeft A M.X ≫ v =
    (A ◁ v) ≫ (φ ▷ B) ≫ μ[B]) :
    baseChange φ M ⟶ B :=
  modTensorDesc A (restrictRegular φ) M ((B ◁ v) ≫ μ[B])
    (splitEvalCond A B φ v hv)

omit [IsCommMonObj A]
  [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair
    (tensorLeft Z)] in
/-- Defining equation of the evaluation. -/
@[reassoc]
theorem modTensorπ_splitEval (hv : actLeft A M.X ≫ v =
    (A ◁ v) ≫ (φ ▷ B) ≫ μ[B]) :
    modTensorπ A (restrictRegular φ) M ≫
        splitEval A B φ v hv = (B ◁ v) ≫ μ[B] :=
  modTensorπ_desc A (restrictRegular φ) M _ _

end Eval

section Coeval

variable (w : M'.X ⟶ B)

/-- A base-linear insertion, bundled as a module morphism into
the restricted regular module. -/
noncomputable def insHom (hw : actLeft A M'.X ≫ w =
    (A ◁ w) ≫ (φ ▷ B) ≫ μ[B]) :
    M' ⟶ restrictRegular φ :=
  Mod.Hom.mk' w (by exact hw)

omit [SymmetricCategory D] [HasCoequalizers D]
  [IsCommMonObj A] [IsCommMonObj B]
  [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair
    (tensorLeft Z)] in
@[simp]
theorem insHom_hom (hw : actLeft A M'.X ≫ w =
    (A ◁ w) ≫ (φ ▷ B) ≫ μ[B]) :
    (insHom A B φ w hw).hom = w := rfl

/-- **The coevaluation core**: swap the pair and push the dual
factor into the algebra — the module tensor product lands in the
base change. -/
noncomputable def splitCoevalCore (hw : actLeft A M'.X ≫ w =
    (A ◁ w) ≫ (φ ▷ B) ≫ μ[B]) :
    modTensor A M M' ⟶ baseChange φ M :=
  modTensorSwap A M M' ≫
    modTensorMap A (insHom A B φ w hw) (𝟙 M)

omit [IsCommMonObj A] [IsCommMonObj B]
  [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair
    (tensorLeft Z)] in
/-- Defining equation of the coevaluation core. -/
@[reassoc]
theorem modTensorπ_splitCoevalCore
    (hw : actLeft A M'.X ≫ w =
      (A ◁ w) ≫ (φ ▷ B) ≫ μ[B]) :
    modTensorπ A M M' ≫ splitCoevalCore A B φ w hw =
      (β_ M.X M'.X).hom ≫ (w ▷ M.X) ≫
        modTensorπ A (restrictRegular φ) M := by
  rw [splitCoevalCore]
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker (modTensorπ_swap A M M') _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine whisker_eq _ ?_
  refine Eq.trans
    (modTensorπ_map A (insHom A B φ w hw) (𝟙 M)) ?_
  exact eq_whisker (by simp) _

end Coeval

section Retract

variable (v : M.X ⟶ B) (w : M'.X ⟶ B)

omit [IsCommMonObj A]
  [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair
    (tensorLeft Z)] in
/-- **Evaluating the coevaluation core multiplies the two
insertions**: the core composite is any descended pair
product. -/
theorem splitCoevalCore_splitEval
    (hv : actLeft A M.X ≫ v =
      (A ◁ v) ≫ (φ ▷ B) ≫ μ[B])
    (hw : actLeft A M'.X ≫ w =
      (A ◁ w) ≫ (φ ▷ B) ≫ μ[B])
    (p : modTensor A M M' ⟶ B)
    (hp : modTensorπ A M M' ≫ p = (v ⊗ₘ w) ≫ μ[B]) :
    splitCoevalCore A B φ w hw ≫ splitEval A B φ v hv =
      p := by
  apply modTensor_hom_ext
  rw [hp, modTensorπ_splitCoevalCore_assoc A B φ w hw]
  have h1 : ((β_ M.X M'.X).hom ≫ (w ▷ M.X) ≫
      modTensorπ A (restrictRegular φ) M) ≫
        splitEval A B φ v hv =
      (β_ M.X M'.X).hom ≫ (w ▷ M.X) ≫ (B ◁ v) ≫ μ[B] := by
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine whisker_eq _ ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    exact whisker_eq _ (modTensorπ_splitEval A B φ v hv)
  have h2 : (β_ M.X M'.X).hom ≫ (w ▷ M.X) ≫
      (B ◁ v) ≫ μ[B] = (v ⊗ₘ w) ≫ μ[B] := by
    rw [← MonoidalCategory.tensorHom_def_assoc,
      ← BraidedCategory.braiding_naturality_assoc,
      IsCommMonObj.mul_comm]
  exact h1.trans h2

omit [IsCommMonObj A] in
/-- **The evaluation is linear over the algebra.** -/
@[reassoc]
theorem baseChangeAct_splitEval
    (hv : actLeft A M.X ≫ v =
      (A ◁ v) ≫ (φ ▷ B) ≫ μ[B]) :
    baseChangeAct φ M ≫ splitEval A B φ v hv =
      (B ◁ splitEval A B φ v hv) ≫ μ[B] := by
  apply modTensor_whisker_hom_ext A (restrictRegular φ) M B
  have h1 : B ◁ modTensorπ A (restrictRegular φ) M ≫
      baseChangeAct φ M ≫ splitEval A B φ v hv =
      ((α_ B B M.X).inv ≫ μ[B] ▷ M.X) ≫
        (B ◁ v) ≫ μ[B] := by
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (eq_whisker
      (whiskerLeft_modTensorπ_baseChangeAct φ M) _) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    exact whisker_eq _ (modTensorπ_splitEval A B φ v hv)
  have h2 : B ◁ modTensorπ A (restrictRegular φ) M ≫
      B ◁ splitEval A B φ v hv ≫ μ[B] =
      (B ◁ ((B ◁ v) ≫ μ[B])) ≫ μ[B] := by
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (eq_whisker
      (MonoidalCategory.whiskerLeft_comp B _ _).symm _) ?_
    exact eq_whisker (congrArg (fun t => B ◁ t)
      (modTensorπ_splitEval A B φ v hv)) _
  have h3 : ((α_ B B M.X).inv ≫ μ[B] ▷ M.X) ≫
      (B ◁ v) ≫ μ[B] =
      (B ◁ ((B ◁ v) ≫ μ[B])) ≫ μ[B] := by
    simp only [MonoidalCategory.whiskerLeft_comp,
      Category.assoc]
    rw [← whisker_exchange_assoc, MonObj.mul_assoc,
      associator_naturality_right_assoc]
    simp
  exact h1.trans (h3.trans h2.symm)

variable (d : ModDualityDatum A M M')

/-- **The coevaluation**: the copair element with its dual
factor pushed into the algebra, multiplied against the
algebra. -/
noncomputable def splitCoeval
    (hw : actLeft A M'.X ≫ w =
      (A ◁ w) ≫ (φ ▷ B) ≫ μ[B]) :
    B ⟶ baseChange φ M :=
  (ρ_ B).inv ≫
    (B ◁ (η[A] ≫ d.copair ≫
      splitCoevalCore A B φ w hw)) ≫
    baseChangeAct φ M

/-- **The coevaluation is linear over the algebra.** -/
@[reassoc]
theorem mul_splitCoeval
    (hw : actLeft A M'.X ≫ w =
      (A ◁ w) ≫ (φ ▷ B) ≫ μ[B]) :
    μ[B] ≫ splitCoeval A B φ w d hw =
      (B ◁ splitCoeval A B φ w d hw) ≫
        baseChangeAct φ M := by
  letI := baseChangeModObj φ M
  have hact : (μ[B] ▷ baseChange φ M) ≫ baseChangeAct φ M =
      (α_ B B (baseChange φ M)).hom ≫
        (B ◁ baseChangeAct φ M) ≫ baseChangeAct φ M :=
    mul_actLeft B (baseChange φ M)
  rw [splitCoeval]
  rw [rightUnitor_inv_naturality_assoc]
  rw [← whisker_exchange_assoc]
  rw [hact]
  simp only [MonoidalCategory.whiskerLeft_comp,
    Category.assoc]
  simp only [associator_naturality_right_assoc]
  rw [reassoc_of% (show (ρ_ (B ⊗ B)).inv ≫
    (α_ B B (𝟙_ D)).hom = B ◁ (ρ_ B).inv from by monoidal)]

/-- **The retract identity** (the dévissage step of the
trichotomy): over splitting data, the coevaluation followed by
the evaluation is the identity — the algebra is a direct factor
of the base change of the module. -/
theorem splitCoeval_splitEval
    (hv : actLeft A M.X ≫ v =
      (A ◁ v) ≫ (φ ▷ B) ≫ μ[B])
    (hw : actLeft A M'.X ≫ w =
      (A ◁ w) ≫ (φ ▷ B) ≫ μ[B])
    (p : modTensor A M M' ⟶ B)
    (hp : modTensorπ A M M' ≫ p = (v ⊗ₘ w) ≫ μ[B])
    (hδ : η[A] ≫ d.copair ≫ p = η[B]) :
    splitCoeval A B φ w d hw ≫ splitEval A B φ v hv =
      𝟙 B := by
  have hx : (η[A] ≫ d.copair ≫
      splitCoevalCore A B φ w hw) ≫
        splitEval A B φ v hv = η[B] := by
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (whisker_eq _ (Category.assoc _ _ _)) ?_
    refine Eq.trans (whisker_eq _ (whisker_eq _
      (splitCoevalCore_splitEval A B φ v w hv hw p hp))) ?_
    exact hδ
  show ((ρ_ B).inv ≫
      (B ◁ (η[A] ≫ d.copair ≫
        splitCoevalCore A B φ w hw)) ≫
      baseChangeAct φ M) ≫ splitEval A B φ v hv = 𝟙 B
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (whisker_eq _ (Category.assoc _ _ _)) ?_
  refine Eq.trans (whisker_eq _ (whisker_eq _
    (baseChangeAct_splitEval A B φ v hv))) ?_
  refine Eq.trans
    (whisker_eq _ (Category.assoc _ _ _).symm) ?_
  refine Eq.trans (whisker_eq _ (eq_whisker
    (MonoidalCategory.whiskerLeft_comp B _ _).symm _)) ?_
  refine Eq.trans (whisker_eq _ (eq_whisker
    (congrArg (fun t => B ◁ t) hx) _)) ?_
  refine Eq.trans (whisker_eq _ (MonObj.mul_one B)) ?_
  exact (ρ_ B).inv_hom_id

/-- The evaluation, as a module morphism onto the regular
module. -/
noncomputable def splitEvalMod
    (hv : actLeft A M.X ≫ v =
      (A ◁ v) ≫ (φ ▷ B) ≫ μ[B]) :
    baseChangeMod φ M ⟶ regularMod B :=
  Mod.Hom.mk' (splitEval A B φ v hv)
    (by exact baseChangeAct_splitEval A B φ v hv)

/-- The coevaluation, as a module morphism from the regular
module. -/
noncomputable def splitCoevalMod
    (hw : actLeft A M'.X ≫ w =
      (A ◁ w) ≫ (φ ▷ B) ≫ μ[B]) :
    regularMod B ⟶ baseChangeMod φ M :=
  Mod.Hom.mk' (splitCoeval A B φ w d hw)
    (by exact mul_splitCoeval A B φ w d hw)

end Retract

end RS
