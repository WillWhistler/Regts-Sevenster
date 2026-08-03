import RS.Classical.Deligne.ChainAlgebra

/-!
# Heterogeneous multiplication of chain colimits

The colimit multiplication of `ChainAlgebra` generalises to three
chains: stagewise multiplications `B i ⊗ C j ⟶ F (i + 1 + j)`
compatible with the three transition families assemble into a
morphism `chainColimit B δB ⊗ chainColimit C δC ⟶ chainColimit F δF`.
The construction is the two-pass `colimit.desc` of the homogeneous
case, verbatim up to the substitution of the three chains: partial
cocones against a fixed stage of `C` in the second slot, then the
total cocone over the second slot through the preservation
isomorphisms.  The defining equation on a pair of stages is
cast-free because the stage inclusions absorb the index transports.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits

universe v u

variable {E : Type u} [Category.{v} E] [MonoidalCategory E]
variable [HasColimitsOfShape SmallNat.{v} E]
variable (B C F : ℕ → E)
variable (δB : ∀ n, B n ⟶ B (n + 1))
variable (δC : ∀ n, C n ⟶ C (n + 1))
variable (δF : ∀ n, F n ⟶ F (n + 1))
variable (mu : ∀ i j : ℕ, B i ⊗ C j ⟶ F (i + 1 + j))
variable (hδl : ∀ i j, (δB i ▷ C j) ≫ mu (i + 1) j =
  mu i j ≫ δF (i + 1 + j) ≫
    chainCast F (Nat.add_right_comm (i + 1) j 1))
variable (hδr : ∀ i j, (B i ◁ δC j) ≫ mu i (j + 1) =
  mu i j ≫ δF (i + 1 + j))

include hδl in
/-- Multiplying after a chain morphism in the first slot agrees with
multiplying first, once both land in the colimit. -/
theorem mulHet_chainMap_ι_left {i i' : ℕ} (h : i ≤ i') (j : ℕ) :
    (chainMap B δB h ▷ C j) ≫ mu i' j ≫
        chainColimitι F δF (i' + 1 + j) =
      mu i j ≫ chainColimitι F δF (i + 1 + j) := by
  induction i', h using Nat.le_induction with
  | base =>
    rw [chainMap_self, MonoidalCategory.id_whiskerRight,
      Category.id_comp]
  | succ i' hii ih =>
    rw [chainMap_succ_of_le B δB hii, comp_whiskerRight,
      Category.assoc, reassoc_of% (hδl i' j),
      chainCast_chainColimitι, delta_chainColimitι]
    exact ih

include hδr in
/-- Multiplying after a chain morphism in the second slot agrees with
multiplying first, once both land in the colimit. -/
theorem mulHet_chainMap_ι_right (i : ℕ) {j j' : ℕ} (h : j ≤ j') :
    (B i ◁ chainMap C δC h) ≫ mu i j' ≫
        chainColimitι F δF (i + 1 + j') =
      mu i j ≫ chainColimitι F δF (i + 1 + j) := by
  induction j', h using Nat.le_induction with
  | base =>
    rw [chainMap_self, MonoidalCategory.whiskerLeft_id,
      Category.id_comp]
  | succ j' hjj ih =>
    rw [chainMap_succ_of_le C δC hjj,
      MonoidalCategory.whiskerLeft_comp, Category.assoc,
      reassoc_of% (hδr i j')]
    have hι : δF (i + 1 + j') ≫
        chainColimitι F δF (i + 1 + (j' + 1)) =
        chainColimitι F δF (i + 1 + j') :=
      delta_chainColimitι F δF (i + 1 + j')
    rw [hι]
    exact ih

/-- The multiply-then-include maps against a fixed stage of `C` in
the second slot form a cocone on the first chain diagram tensored on
the right with that stage. -/
noncomputable def chainMulHetCocone (j : ℕ) :
    Cocone (chainDiagram B δB ⋙ tensorRight (C j)) where
  pt := chainColimit F δF
  ι :=
    { app := fun k =>
        mu (smallNatEquiv.inverse.obj k) j ≫
          chainColimitι F δF (smallNatEquiv.inverse.obj k + 1 + j)
      naturality := fun {k k'} f => by
        show (chainMap B δB
            (leOfHom (smallNatEquiv.inverse.map f)) ▷ C j) ≫
            (mu (smallNatEquiv.inverse.obj k') j ≫
              chainColimitι F δF
                (smallNatEquiv.inverse.obj k' + 1 + j)) =
          (mu (smallNatEquiv.inverse.obj k) j ≫
            chainColimitι F δF
              (smallNatEquiv.inverse.obj k + 1 + j)) ≫
            𝟙 (chainColimit F δF)
        rw [Category.comp_id]
        exact mulHet_chainMap_ι_left B C F δB δF mu hδl
          (leOfHom (smallNatEquiv.inverse.map f)) j }

variable
  [∀ X : E, PreservesColimitsOfShape SmallNat.{v} (tensorRight X)]

/-- Partial multiplication of the first chain colimit against a
fixed stage of `C` in the second slot. -/
noncomputable def chainMulHetStage (j : ℕ) :
    chainColimit B δB ⊗ C j ⟶ chainColimit F δF :=
  ((preservesColimitIso (tensorRight (C j))
      (chainDiagram B δB)).hom ≫
    colimit.desc _ (chainMulHetCocone B C F δB δF mu hδl j) :
    (tensorRight (C j)).obj (colimit (chainDiagram B δB)) ⟶
      chainColimit F δF)

/-- On a stage, the partial multiplication is multiply-then-include. -/
@[reassoc]
theorem ι_chainMulHetStage (i j : ℕ) :
    (chainColimitι B δB i ▷ C j) ≫
        chainMulHetStage B C F δB δF mu hδl j =
      mu i j ≫ chainColimitι F δF (i + 1 + j) := by
  show (tensorRight (C j)).map (colimit.ι (chainDiagram B δB)
      (smallNatEquiv.functor.obj i)) ≫
      chainMulHetStage B C F δB δF mu hδl j =
    mu i j ≫ chainColimitι F δF (i + 1 + j)
  rw [chainMulHetStage, ι_preservesColimitIso_hom_assoc]
  exact colimit.ι_desc (chainMulHetCocone B C F δB δF mu hδl j)
    (smallNatEquiv.functor.obj i)

include hδr in
/-- The partial multiplications are natural in the stage. -/
@[reassoc]
theorem chainMulHetStage_natural {j j' : ℕ} (h : j ≤ j') :
    (chainColimit B δB ◁ chainMap C δC h) ≫
        chainMulHetStage B C F δB δF mu hδl j' =
      chainMulHetStage B C F δB δF mu hδl j := by
  apply chainColimit_tensorRight_hom_ext B δB
  intro i
  rw [← Category.assoc, ← whisker_exchange, Category.assoc,
    ι_chainMulHetStage, ι_chainMulHetStage]
  exact mulHet_chainMap_ι_right B C F δC δF mu hδr i h

variable
  [∀ X : E, PreservesColimitsOfShape SmallNat.{v} (tensorLeft X)]

/-- The partial multiplications form a cocone on the second chain
diagram tensored on the left with the first chain colimit. -/
noncomputable def chainMulHetTotalCocone :
    Cocone (chainDiagram C δC ⋙ tensorLeft (chainColimit B δB))
    where
  pt := chainColimit F δF
  ι :=
    { app := fun k =>
        chainMulHetStage B C F δB δF mu hδl
          (smallNatEquiv.inverse.obj k)
      naturality := fun {k k'} f => by
        show (chainColimit B δB ◁ chainMap C δC
            (leOfHom (smallNatEquiv.inverse.map f))) ≫
            chainMulHetStage B C F δB δF mu hδl
              (smallNatEquiv.inverse.obj k') =
          chainMulHetStage B C F δB δF mu hδl
              (smallNatEquiv.inverse.obj k) ≫
            𝟙 (chainColimit F δF)
        rw [Category.comp_id]
        exact chainMulHetStage_natural B C F δB δC δF mu hδl hδr
          (leOfHom (smallNatEquiv.inverse.map f)) }

/-- **The heterogeneous colimit multiplication**: the partial
multiplications assembled over the second slot. -/
noncomputable def chainColimitMulHet :
    chainColimit B δB ⊗ chainColimit C δC ⟶ chainColimit F δF :=
  ((preservesColimitIso (tensorLeft (chainColimit B δB))
      (chainDiagram C δC)).hom ≫
    colimit.desc _
      (chainMulHetTotalCocone B C F δB δC δF mu hδl hδr) :
    (tensorLeft (chainColimit B δB)).obj
        (colimit (chainDiagram C δC)) ⟶
      chainColimit F δF)

/-- On a stage in the second slot, the heterogeneous colimit
multiplication is the partial multiplication. -/
@[reassoc]
theorem whiskerLeft_ι_chainColimitMulHet (j : ℕ) :
    (chainColimit B δB ◁ chainColimitι C δC j) ≫
        chainColimitMulHet B C F δB δC δF mu hδl hδr =
      chainMulHetStage B C F δB δF mu hδl j := by
  show (tensorLeft (chainColimit B δB)).map
      (colimit.ι (chainDiagram C δC)
        (smallNatEquiv.functor.obj j)) ≫
      chainColimitMulHet B C F δB δC δF mu hδl hδr =
    chainMulHetStage B C F δB δF mu hδl j
  rw [chainColimitMulHet, ι_preservesColimitIso_hom_assoc]
  exact colimit.ι_desc
    (chainMulHetTotalCocone B C F δB δC δF mu hδl hδr)
    (smallNatEquiv.functor.obj j)

/-- **Defining equation of the heterogeneous colimit
multiplication**: on a pair of stages it is multiply-then-include. -/
@[reassoc]
theorem ι_tensorHom_chainColimitMulHet (i j : ℕ) :
    (chainColimitι B δB i ⊗ₘ chainColimitι C δC j) ≫
        chainColimitMulHet B C F δB δC δF mu hδl hδr =
      mu i j ≫ chainColimitι F δF (i + 1 + j) := by
  rw [tensorHom_def, Category.assoc,
    whiskerLeft_ι_chainColimitMulHet, ι_chainMulHetStage]

end RS
