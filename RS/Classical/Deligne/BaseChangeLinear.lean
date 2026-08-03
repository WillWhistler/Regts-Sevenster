import RS.Classical.Deligne.BaseChangeTensor
import RS.Classical.Deligne.BaseChangeBiprod

/-!
# Linearity of the base-changed pairing and copairing

The base-changed pairing and copairing of a duality datum are
linear over the new base: each factor of the defining composites
intertwines the descended actions, and the two linearity laws
follow by chaining the factors.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  [SymmetricCategory D]
variable [HasCoequalizers D]
variable [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair
  (tensorLeft Z)]
variable [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair
  (tensorRight Z)]
variable (A : D) [MonObj A] [IsCommMonObj A]
variable (B : D) [MonObj B] [IsCommMonObj B]
variable (φ : A ⟶ B) [IsMonHom φ]

section Glue

omit [SymmetricCategory D] [HasCoequalizers D]
  [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair
    (tensorLeft Z)]
  [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair
    (tensorRight Z)] [MonObj B] [IsCommMonObj B] in
/-- A composite of `B`-linear morphisms is `B`-linear. -/
private theorem comp_linear {X Y Z : D}
    {aX : B ⊗ X ⟶ X} {aY : B ⊗ Y ⟶ Y} {aZ : B ⊗ Z ⟶ Z}
    {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : aX ≫ f = (B ◁ f) ≫ aY)
    (hg : aY ≫ g = (B ◁ g) ≫ aZ) :
    aX ≫ (f ≫ g) = (B ◁ (f ≫ g)) ≫ aZ :=
  calc aX ≫ f ≫ g = (aX ≫ f) ≫ g := (Category.assoc _ _ _).symm
    _ = ((B ◁ f) ≫ aY) ≫ g := eq_whisker hf g
    _ = (B ◁ f) ≫ aY ≫ g := Category.assoc _ _ _
    _ = (B ◁ f) ≫ (B ◁ g) ≫ aZ := whisker_eq _ hg
    _ = ((B ◁ f) ≫ (B ◁ g)) ≫ aZ := (Category.assoc _ _ _).symm
    _ = (B ◁ (f ≫ g)) ≫ aZ :=
        eq_whisker (MonoidalCategory.whiskerLeft_comp B f g).symm _

omit [SymmetricCategory D] [HasCoequalizers D]
  [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair
    (tensorLeft Z)]
  [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair
    (tensorRight Z)] [MonObj B] [IsCommMonObj B] in
/-- The inverse of a `B`-linear isomorphism is `B`-linear. -/
private theorem inv_linear_of_hom_linear {X Y : D} (e : X ≅ Y)
    {aX : B ⊗ X ⟶ X} {aY : B ⊗ Y ⟶ Y}
    (h : aX ≫ e.hom = (B ◁ e.hom) ≫ aY) :
    aY ≫ e.inv = (B ◁ e.inv) ≫ aX := by
  rw [← cancel_mono e.hom, Category.assoc, Category.assoc,
    e.inv_hom_id, Category.comp_id, h, ← Category.assoc,
    ← MonoidalCategory.whiskerLeft_comp, e.inv_hom_id,
    MonoidalCategory.whiskerLeft_id, Category.id_comp]

end Glue

section Ext

variable (M N : Mod D A)

omit [MonObj B] [IsCommMonObj B] [IsCommMonObj A] in
/-- Whiskering the module-tensor coequalizer by `tensorLeft P`
and then by `tensorRight W` yields a colimit cofork. -/
noncomputable def modTensorWhiskerLRIsColimit (P W : D) :
    IsColimit (Cofork.ofπ ((P ◁ modTensorπ A M N) ▷ W)
      (by rw [← MonoidalCategory.comp_whiskerRight,
        ← MonoidalCategory.whiskerLeft_comp,
        modTensor_condition,
        MonoidalCategory.whiskerLeft_comp,
        MonoidalCategory.comp_whiskerRight]) :
      Cofork ((P ◁ modTensorLegM A M N) ▷ W)
        ((P ◁ modTensorLegN A M N) ▷ W)) :=
  isColimitOfHasCoequalizerOfPreservesColimit
    (tensorLeft P ⋙ tensorRight W) _ _

omit [MonObj B] [IsCommMonObj B] [IsCommMonObj A]
  [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair
    (tensorRight Z)] in
/-- Morphisms out of a left-then-right whiskered tensor product
of modules are determined by the doubly whiskered projection. -/
lemma modTensor_whiskerLR_hom_ext (P W : D) {Z : D}
    {k l : (P ⊗ modTensor A M N) ⊗ W ⟶ Z}
    (h : ((P ◁ modTensorπ A M N) ▷ W) ≫ k =
      ((P ◁ modTensorπ A M N) ▷ W) ≫ l) : k = l :=
  Cofork.IsColimit.hom_ext
    (modTensorWhiskerLRIsColimit A M N P W) h

end Ext

section Collapse

variable (P : Mod D B) (N : Mod D A)

omit [HasCoequalizers D]
  [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair
    (tensorLeft Z)]
  [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair
    (tensorRight Z)] [MonObj A] [IsCommMonObj A] in
/-- The `B`-action on a `B`-module commutes with the braided
right action through the base morphism. -/
theorem restrictAct_compat :
    B ◁ ((P.X ◁ φ) ≫ actRight B P.X) ≫ actLeft B P.X =
      (α_ B P.X A).inv ≫ actLeft B P.X ▷ A ≫
        ((P.X ◁ φ) ≫ actRight B P.X) := by
  rw [MonoidalCategory.whiskerLeft_comp, Category.assoc,
    actLeft_actRight B P.X,
    associator_inv_naturality_right_assoc,
    whisker_exchange_assoc]

/-- **The descended `B`-action on the collapsed tensor**: the
`B`-action of the module descends through the coequalizer of the
restricted-module tensor. -/
noncomputable def collapseAct :
    B ⊗ modTensor A (restrictMod A B φ P) N ⟶
      modTensor A (restrictMod A B φ P) N :=
  modTensorDescAct A (restrictMod A B φ P) N B (actLeft B P.X)
    (by
      rw [actRight_restrictMod]
      exact restrictAct_compat A B φ P)

omit [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair
  (tensorRight Z)] [IsCommMonObj A] in
/-- Defining equation of the descended `B`-action, in the retyped
spelling. -/
theorem whiskerLeft_restrictπ_collapseAct :
    B ◁ restrictπ A B φ P N ≫ collapseAct A B φ P N =
      ((α_ B P.X N.X).inv ≫ actLeft B P.X ▷ N.X) ≫
        restrictπ A B φ P N := by
  exact whiskerLeft_modTensorπ_descAct A (restrictMod A B φ P) N
    B (actLeft B P.X) _

omit [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair
  (tensorRight Z)] [IsCommMonObj A] in
/-- The half-descended collapse intertwines the module action
with the descended action. -/
theorem collapseMid_linear :
    (actLeft B P.X ▷ baseChange φ N) ≫ collapseMid A B φ P N =
      (α_ B P.X (baseChange φ N)).hom ≫
        (B ◁ collapseMid A B φ P N) ≫ collapseAct A B φ P N := by
  apply modTensor_whisker_hom_ext A (restrictRegular φ) N
    (B ⊗ P.X)
  have hL : ((B ⊗ P.X) ◁ modTensorπ A (restrictRegular φ) N) ≫
      ((actLeft B P.X ▷ baseChange φ N) ≫
        collapseMid A B φ P N) =
      (actLeft B P.X ▷ (B ⊗ N.X)) ≫ collapseCover A B φ P N := by
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (eq_whisker (whisker_exchange
      (actLeft B P.X) (modTensorπ A (restrictRegular φ) N)) _) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    exact whisker_eq _ (whiskerLeft_collapseMid A B φ P N)
  have hR : ((B ⊗ P.X) ◁ modTensorπ A (restrictRegular φ) N) ≫
      ((α_ B P.X (baseChange φ N)).hom ≫
        (B ◁ collapseMid A B φ P N) ≫ collapseAct A B φ P N) =
      (α_ B P.X (B ⊗ N.X)).hom ≫
        (B ◁ collapseCover A B φ P N) ≫
          collapseAct A B φ P N := by
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (eq_whisker (associator_naturality_right
      B P.X (modTensorπ A (restrictRegular φ) N)) _) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine whisker_eq _ ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (eq_whisker
      (MonoidalCategory.whiskerLeft_comp B _ _).symm _) ?_
    exact eq_whisker (congrArg (fun t => B ◁ t)
      (whiskerLeft_collapseMid A B φ P N)) _
  refine hL.trans (Eq.trans ?_ hR.symm)
  rw [collapseCover]
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
  rw [whiskerLeft_restrictπ_collapseAct]
  simp only [Category.assoc]
  rw [associator_inv_naturality_middle_assoc,
    ← MonoidalCategory.comp_whiskerRight_assoc,
    actLeft_actRight B P.X]
  simp only [MonoidalCategory.comp_whiskerRight, Category.assoc]
  rw [associator_inv_naturality_left_assoc]
  rw [reassoc_of% (show (α_ B P.X (B ⊗ N.X)).hom ≫
    (B ◁ (α_ P.X B N.X).inv) ≫ (α_ B (P.X ⊗ B) N.X).inv ≫
      ((α_ B P.X B).inv ▷ N.X) = (α_ (B ⊗ P.X) B N.X).inv
    from by monoidal)]

end Collapse

section Hom

variable (P : Mod D B) (N : Mod D A)

omit [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair
  (tensorRight Z)] [IsCommMonObj A] in
/-- **The collapse is linear over the new base**: it intertwines
the module action with the descended action. -/
theorem collapseHom_linear :
    modTensorAct B P (baseChangeMod φ N) ≫
        collapseHom A B φ P N =
      (B ◁ collapseHom A B φ P N) ≫ collapseAct A B φ P N := by
  apply modTensor_whisker_hom_ext B P (baseChangeMod φ N) B
  have hL : (B ◁ bcπ A B φ P N) ≫
      modTensorAct B P (baseChangeMod φ N) ≫
        collapseHom A B φ P N =
      ((α_ B P.X (baseChange φ N)).inv ≫
        (actLeft B P.X ▷ baseChange φ N)) ≫
        collapseMid A B φ P N := by
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (eq_whisker
      (whiskerLeft_modTensorπ_act B P
        (baseChangeMod φ N)) _) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    exact whisker_eq _ (modTensorπ_collapseHom A B φ P N)
  have hR : (B ◁ bcπ A B φ P N) ≫
      (B ◁ collapseHom A B φ P N) ≫ collapseAct A B φ P N =
      (B ◁ collapseMid A B φ P N) ≫ collapseAct A B φ P N := by
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (eq_whisker
      (MonoidalCategory.whiskerLeft_comp B _ _).symm _) ?_
    exact eq_whisker (congrArg (fun t => B ◁ t)
      (modTensorπ_collapseHom A B φ P N)) _
  refine hL.trans (Eq.trans ?_ hR.symm)
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (whisker_eq _
    (collapseMid_linear A B φ P N)) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker (Iso.inv_hom_id _) _) ?_
  exact Category.id_comp _

end Hom

section UnitLeg

omit [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair
  (tensorRight Z)] in
/-- The right unit collapse of the induced regular module is
linear over the new base. -/
theorem baseChangeAct_unitRight :
    baseChangeAct φ (regularMod A) ≫
        (modTensorUnitRight A (restrictRegular φ)).hom =
      (B ◁ (modTensorUnitRight A (restrictRegular φ)).hom) ≫
        μ[B] := by
  apply modTensor_whisker_hom_ext A (restrictRegular φ)
    (regularMod A) B
  have hπ : modTensorπ A (restrictRegular φ) (regularMod A) ≫
      (modTensorUnitRight A (restrictRegular φ)).hom =
      (B ◁ φ) ≫ μ[B] := by
    refine Eq.trans (modTensorπ_desc A (restrictRegular φ)
      (regularMod A) _ _) ?_
    exact actRight_restrictRegular φ
  have hL : (B ◁ modTensorπ A (restrictRegular φ)
      (regularMod A)) ≫ baseChangeAct φ (regularMod A) ≫
      (modTensorUnitRight A (restrictRegular φ)).hom =
      ((α_ B B A).inv ≫ (μ[B] ▷ A)) ≫ ((B ◁ φ) ≫ μ[B]) := by
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (eq_whisker
      (whiskerLeft_modTensorπ_baseChangeAct φ
        (regularMod A)) _) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    exact whisker_eq _ hπ
  have hR : (B ◁ modTensorπ A (restrictRegular φ)
      (regularMod A)) ≫
      (B ◁ (modTensorUnitRight A (restrictRegular φ)).hom) ≫
        μ[B] =
      (B ◁ ((B ◁ φ) ≫ μ[B])) ≫ μ[B] := by
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (eq_whisker
      (MonoidalCategory.whiskerLeft_comp B _ _).symm _) ?_
    exact eq_whisker (congrArg (fun t => B ◁ t) hπ) _
  refine hL.trans (Eq.trans ?_ hR.symm)
  simp only [MonoidalCategory.whiskerLeft_comp,
    Category.assoc]
  rw [MonObj.mul_assoc_flip,
    associator_inv_naturality_right_assoc,
    whisker_exchange_assoc]

end UnitLeg

section Cast

omit [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair
  (tensorRight Z)] [IsCommMonObj A] [MonObj B]
  [IsCommMonObj B] in
/-- **Transport of a descended action along an equality of
modules**: the descended actions of equal modules agree through
the induced transport. -/
theorem modTensorDescAct_cast {P Q : Mod D A} (h : P = Q)
    (N : Mod D A) (actP : B ⊗ P.X ⟶ P.X)
    (actQ : B ⊗ Q.X ⟶ Q.X)
    (hcP : B ◁ actRight A P.X ≫ actP =
      (α_ B P.X A).inv ≫ actP ▷ A ≫ actRight A P.X)
    (hcQ : B ◁ actRight A Q.X ≫ actQ =
      (α_ B Q.X A).inv ≫ actQ ▷ A ≫ actRight A Q.X)
    (hact : actP ≫ eqToHom (congrArg Mod.X h) =
      (B ◁ eqToHom (congrArg Mod.X h)) ≫ actQ) :
    modTensorDescAct A P N B actP hcP ≫
        eqToHom (congrArg (fun R => modTensor A R N) h) =
      (B ◁ eqToHom (congrArg (fun R => modTensor A R N) h)) ≫
        modTensorDescAct A Q N B actQ hcQ := by
  subst h
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp,
    MonoidalCategory.whiskerLeft_id] at hact ⊢
  subst hact
  rfl

end Cast

section AssocLeg

variable (M N : Mod D A)

/-- The base-change action, retyped at the relative-tensor
spelling so that goals stay type-correct. -/
noncomputable def bcActR :
    B ⊗ modTensor A (restrictRegular φ) M ⟶
      modTensor A (restrictRegular φ) M :=
  baseChangeAct φ M

omit [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair
  (tensorRight Z)] [IsCommMonObj A] in
/-- Defining equation of the retyped base-change action. -/
theorem whiskerLeft_π_bcActR :
    (B ◁ modTensorπ A (restrictRegular φ) M) ≫
        bcActR A B φ M =
      ((α_ B B M.X).inv ≫ (μ[B] ▷ M.X)) ≫
        modTensorπ A (restrictRegular φ) M :=
  whiskerLeft_modTensorπ_baseChangeAct φ M

/-- The retyped base-change action commutes with the braided
right action. -/
theorem bcActR_compat :
    B ◁ actRight A (modTensorMod A (restrictRegular φ) M).X ≫
        bcActR A B φ M =
      (α_ B (modTensorMod A (restrictRegular φ) M).X A).inv ≫
        (bcActR A B φ M ▷ A) ≫
        actRight A
          (modTensorMod A (restrictRegular φ) M).X := by
  have key : ∀ {Z : D} (g : B ⊗ M.X ⟶ Z),
      (B ◁ (α_ B M.X A).hom) ≫
        (B ◁ (B ◁ actRight A M.X)) ≫
        ((α_ B B M.X).inv ≫ (μ[B] ▷ M.X)) ≫ g =
      (α_ B (B ⊗ M.X) A).inv ≫
        (((α_ B B M.X).inv ≫ (μ[B] ▷ M.X)) ▷ A) ≫
        (α_ B M.X A).hom ≫ (B ◁ actRight A M.X) ≫ g := by
    intro Z g
    simp only [MonoidalCategory.comp_whiskerRight,
      Category.assoc]
    rw [associator_inv_naturality_right_assoc,
      whisker_exchange_assoc]
    rw [associator_naturality_left_assoc]
    rw [reassoc_of% (show (B ◁ (α_ B M.X A).hom) ≫
      (α_ B B (M.X ⊗ A)).inv = (α_ B (B ⊗ M.X) A).inv ≫
        ((α_ B B M.X).inv ▷ A) ≫ (α_ (B ⊗ B) M.X A).hom
      from by monoidal)]
  have hπa : (modTensorπ A (restrictRegular φ) M ▷ A) ≫
      actRight A (modTensorMod A (restrictRegular φ) M).X =
      (α_ B M.X A).hom ≫ (B ◁ actRight A M.X) ≫
        modTensorπ A (restrictRegular φ) M :=
    modTensorπ_actRight A (restrictRegular φ) M
  have step : (B ◁ ((modTensorπ A (restrictRegular φ) M ▷ A)
      ≫ actRight A
        (modTensorMod A (restrictRegular φ) M).X)) =
      (B ◁ (α_ B M.X A).hom) ≫
        (B ◁ (B ◁ actRight A M.X)) ≫
        (B ◁ modTensorπ A (restrictRegular φ) M) :=
    (congrArg (fun t => B ◁ t) hπa).trans
      ((MonoidalCategory.whiskerLeft_comp B _ _).trans
        (whisker_eq _
          (MonoidalCategory.whiskerLeft_comp B _ _)))
  refine (cancel_epi (B ◁ (modTensorπ A (restrictRegular φ) M
    ▷ A))).mp ?_
  have hL : (B ◁ (modTensorπ A (restrictRegular φ) M ▷ A)) ≫
      (B ◁ actRight A
        (modTensorMod A (restrictRegular φ) M).X ≫
        bcActR A B φ M) =
      (B ◁ (α_ B M.X A).hom) ≫
        (B ◁ (B ◁ actRight A M.X)) ≫
        ((α_ B B M.X).inv ≫ (μ[B] ▷ M.X)) ≫
        modTensorπ A (restrictRegular φ) M := by
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (eq_whisker
      (MonoidalCategory.whiskerLeft_comp B _ _).symm _) ?_
    refine Eq.trans (eq_whisker step _) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine whisker_eq _ ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    exact whisker_eq _ (whiskerLeft_π_bcActR A B φ M)
  have hR : (B ◁ (modTensorπ A (restrictRegular φ) M ▷ A)) ≫
      ((α_ B (modTensorMod A (restrictRegular φ) M).X A).inv ≫
        (bcActR A B φ M ▷ A) ≫
        actRight A
          (modTensorMod A (restrictRegular φ) M).X) =
      (α_ B (B ⊗ M.X) A).inv ≫
        (((α_ B B M.X).inv ≫ (μ[B] ▷ M.X)) ▷ A) ≫
        (α_ B M.X A).hom ≫ (B ◁ actRight A M.X) ≫
        modTensorπ A (restrictRegular φ) M := by
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (eq_whisker
      (associator_inv_naturality_middle B
        (modTensorπ A (restrictRegular φ) M) A) _) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine whisker_eq _ ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (eq_whisker
      (MonoidalCategory.comp_whiskerRight _ _ _).symm _) ?_
    refine Eq.trans (eq_whisker (congrArg
      (fun t => t ▷ A) (whiskerLeft_π_bcActR A B φ M)) _) ?_
    refine Eq.trans (eq_whisker
      (MonoidalCategory.comp_whiskerRight _ _ _) _) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    exact whisker_eq _ hπa
  exact hL.trans ((key _).trans hR.symm)

/-- **The associator is linear over the new base**: it
intertwines the action descended on the nested first slot with
the action of the base change. -/
theorem assocHom_linear
    (hc : B ◁ actRight A
        (modTensorMod A (restrictRegular φ) M).X ≫
        bcActR A B φ M =
      (α_ B (modTensorMod A (restrictRegular φ) M).X A).inv ≫
        (bcActR A B φ M ▷ A) ≫
        actRight A
          (modTensorMod A (restrictRegular φ) M).X) :
    modTensorDescAct A (modTensorMod A (restrictRegular φ) M) N
        B (bcActR A B φ M) hc ≫
        modTensorAssocHom A (restrictRegular φ) M N =
      (B ◁ modTensorAssocHom A (restrictRegular φ) M N) ≫
        bcActR A B φ (modTensorMod A M N) := by
  apply modTensor_whisker_hom_ext A
    (modTensorMod A (restrictRegular φ) M) N B
  have hL : (B ◁ modTensorπ A
      (modTensorMod A (restrictRegular φ) M) N) ≫
      (modTensorDescAct A
        (modTensorMod A (restrictRegular φ) M) N B
        (bcActR A B φ M) hc ≫
        modTensorAssocHom A (restrictRegular φ) M N) =
      ((α_ B (modTensor A (restrictRegular φ) M) N.X).inv ≫
        (bcActR A B φ M ▷ N.X)) ≫
        modTensorAssocMid A (restrictRegular φ) M N := by
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (eq_whisker
      (whiskerLeft_modTensorπ_descAct A
        (modTensorMod A (restrictRegular φ) M) N B
        (bcActR A B φ M) hc) _) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    exact whisker_eq _
      (modTensorπ_assocHom A (restrictRegular φ) M N)
  have hR : (B ◁ modTensorπ A
      (modTensorMod A (restrictRegular φ) M) N) ≫
      ((B ◁ modTensorAssocHom A (restrictRegular φ) M N) ≫
        bcActR A B φ (modTensorMod A M N)) =
      (B ◁ modTensorAssocMid A (restrictRegular φ) M N) ≫
        bcActR A B φ (modTensorMod A M N) := by
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (eq_whisker
      (MonoidalCategory.whiskerLeft_comp B _ _).symm _) ?_
    exact eq_whisker (congrArg (fun t => B ◁ t)
      (modTensorπ_assocHom A (restrictRegular φ) M N)) _
  refine hL.trans (Eq.trans ?_ hR.symm)
  refine (cancel_epi (B ◁ (modTensorπ A (restrictRegular φ) M
    ▷ N.X))).mp ?_
  simp only [Category.assoc]
  rw [associator_inv_naturality_middle_assoc]
  rw [← MonoidalCategory.comp_whiskerRight_assoc]
  rw [whiskerLeft_π_bcActR]
  simp only [MonoidalCategory.comp_whiskerRight,
    Category.assoc]
  rw [whiskerRight_modTensorπ_assocMid]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc,
    whiskerRight_modTensorπ_assocMid]
  rw [modTensorAssocCover]
  simp only [MonoidalCategory.whiskerLeft_comp,
    Category.assoc]
  refine Eq.trans ?_ (whisker_eq _ (whisker_eq _
    (whiskerLeft_π_bcActR A B φ
      (modTensorMod A M N)))).symm
  have key : ∀ {Z : D} (g : B ⊗ modTensor A M N ⟶ Z),
      (α_ B (B ⊗ M.X) N.X).inv ≫
        ((α_ B B M.X).inv ▷ N.X) ≫
        ((μ[B] ▷ M.X) ▷ N.X) ≫
        (α_ B M.X N.X).hom ≫
        (B ◁ modTensorπ A M N) ≫ g =
      (B ◁ (α_ B M.X N.X).hom) ≫
        (B ◁ (B ◁ modTensorπ A M N)) ≫
        ((α_ B B (modTensor A M N)).inv ≫
          (μ[B] ▷ modTensor A M N)) ≫ g := by
    intro Z g
    simp only [Category.assoc]
    rw [associator_inv_naturality_right_assoc,
      whisker_exchange_assoc]
    rw [associator_naturality_left_assoc]
    rw [reassoc_of% (show (α_ B (B ⊗ M.X) N.X).inv ≫
      ((α_ B B M.X).inv ▷ N.X) ≫ (α_ (B ⊗ B) M.X N.X).hom =
      (B ◁ (α_ B M.X N.X).hom) ≫ (α_ B B (M.X ⊗ N.X)).inv
      from by monoidal)]
  exact key _

end AssocLeg

section ProjFormula

variable (M N : Mod D A)

/-- **The projection formula is linear over the new base.** -/
theorem projFormula_linear :
    modTensorAct B (baseChangeMod φ M) (baseChangeMod φ N) ≫
        (projFormula A B φ M N).hom =
      (B ◁ (projFormula A B φ M N).hom) ≫
        baseChangeAct φ (modTensorMod A M N) := by
  have hcast : collapseAct A B φ (baseChangeMod φ M) N ≫
      eqToHom (congrArg (fun P => modTensor A P N)
        (restrictMod_baseChange_eq A B φ M)) =
      (B ◁ eqToHom (congrArg (fun P => modTensor A P N)
        (restrictMod_baseChange_eq A B φ M))) ≫
        modTensorDescAct A
          (modTensorMod A (restrictRegular φ) M) N B
          (bcActR A B φ M) (bcActR_compat A B φ M) := by
    have hact : bcActR A B φ M ≫
        𝟙 (modTensor A (restrictRegular φ) M) =
        (B ◁ 𝟙 (modTensor A (restrictRegular φ) M)) ≫
          bcActR A B φ M := by
      rw [Category.comp_id, MonoidalCategory.whiskerLeft_id,
        Category.id_comp]
    exact modTensorDescAct_cast A B
      (restrictMod_baseChange_eq A B φ M) N _ _ _ _ hact
  show modTensorAct B (baseChangeMod φ M)
      (baseChangeMod φ N) ≫
      (collapseHom A B φ (baseChangeMod φ M) N ≫
        eqToHom (congrArg (fun P => modTensor A P N)
          (restrictMod_baseChange_eq A B φ M)) ≫
        modTensorAssocHom A (restrictRegular φ) M N) =
    (B ◁ (collapseHom A B φ (baseChangeMod φ M) N ≫
      eqToHom (congrArg (fun P => modTensor A P N)
        (restrictMod_baseChange_eq A B φ M)) ≫
      modTensorAssocHom A (restrictRegular φ) M N)) ≫
      baseChangeAct φ (modTensorMod A M N)
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker
    (collapseHom_linear A B φ (baseChangeMod φ M) N) _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (whisker_eq _
    (Category.assoc _ _ _).symm) ?_
  refine Eq.trans (whisker_eq _ (eq_whisker hcast _)) ?_
  refine Eq.trans (whisker_eq _ (Category.assoc _ _ _)) ?_
  refine Eq.trans (whisker_eq _ (whisker_eq _
    (assocHom_linear A B φ M N
      (bcActR_compat A B φ M)))) ?_
  refine Eq.symm ?_
  refine Eq.trans (eq_whisker
    (MonoidalCategory.whiskerLeft_comp B _ _) _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine whisker_eq _ ?_
  refine Eq.trans (eq_whisker
    (MonoidalCategory.whiskerLeft_comp B _ _) _) ?_
  exact Category.assoc _ _ _

end ProjFormula

end RS
