import RS.Novel.Envelope.EnvAbelian
import RS.Novel.Envelope.KaroubiMonoidal
import RS.Novel.Envelope.MatMonoidal

/-!
# Monoidal preadditivity and linearity through the tower

The skein tensor is a bundled bilinear map, so the skein category
is monoidal-preadditive and monoidal-linear; both properties lift
through the Karoubi and matrix layers entrywise, giving the full
instance chain for the envelope.
-/

namespace RS

open CategoryTheory CategoryTheory.Idempotents
open MonoidalCategory

variable {R : ℕ} (f : EdgeRankParameter R)

/-! ### The skein base -/

/-- The skein tensor is additive in each argument. -/
instance skeinMonoidalPreadditive :
    MonoidalPreadditive (SkeinObj f) where
  whiskerLeft_zero := by
    intro X Y Z
    show (HomSpace.tensor f X.arity X.arity Y.arity Z.arity
      (HomSpace.ofFragment f.val (strandBundle X.arity))) 0 = 0
    rw [map_zero]
  zero_whiskerRight := by
    intro X Y Z
    show (HomSpace.tensor f Y.arity Z.arity X.arity X.arity) 0
      (HomSpace.ofFragment f.val (strandBundle X.arity)) = 0
    rw [map_zero]
    rfl
  whiskerLeft_add := by
    intro X Y Z g g'
    show (HomSpace.tensor f X.arity X.arity Y.arity Z.arity
      (HomSpace.ofFragment f.val (strandBundle X.arity)))
      (g + g') = _
    rw [map_add]
    rfl
  add_whiskerRight := by
    intro X Y Z g g'
    show (HomSpace.tensor f Y.arity Z.arity X.arity X.arity)
      (g + g')
      (HomSpace.ofFragment f.val (strandBundle X.arity)) = _
    rw [map_add]
    rfl

/-- And ℂ-linear in each argument, being a bundled bilinear map. -/
instance skeinMonoidalLinear :
    MonoidalLinear ℂ (SkeinObj f) where
  whiskerLeft_smul := by
    intro X Y Z c g
    show (HomSpace.tensor f X.arity X.arity Y.arity Z.arity
      (HomSpace.ofFragment f.val (strandBundle X.arity)))
      (c • g) = _
    rw [map_smul]
    rfl
  smul_whiskerRight := by
    intro c X Y g Z
    show (HomSpace.tensor f X.arity Y.arity Z.arity Z.arity)
      (c • g)
      (HomSpace.ofFragment f.val (strandBundle Z.arity)) = _
    rw [map_smul]
    rfl

/-! ### The Karoubi lift (general) -/

section KaroubiLift

variable (C : Type*) [Category C] [Preadditive C]
  [MonoidalCategory C] [MonoidalPreadditive C]

/-- Monoidal preadditivity lifts to the Karoubi envelope, where
tensoring acts on underlying morphisms. -/
instance karoubiMonoidalPreadditive :
    MonoidalPreadditive (Karoubi C) where
  whiskerLeft_zero := by
    intro X Y Z
    apply Karoubi.hom_ext
    show X.p ⊗ₘ (0 : Y.X ⟶ Z.X) = 0
    rw [MonoidalPreadditive.tensor_zero]
  zero_whiskerRight := by
    intro X Y Z
    apply Karoubi.hom_ext
    show (0 : Y.X ⟶ Z.X) ⊗ₘ X.p = 0
    rw [MonoidalPreadditive.zero_tensor]
  whiskerLeft_add := by
    intro X Y Z g g'
    apply Karoubi.hom_ext
    show X.p ⊗ₘ (g.f + g'.f) = X.p ⊗ₘ g.f + X.p ⊗ₘ g'.f
    rw [MonoidalPreadditive.tensor_add]
  add_whiskerRight := by
    intro X Y Z g g'
    apply Karoubi.hom_ext
    show (g.f + g'.f) ⊗ₘ X.p = g.f ⊗ₘ X.p + g'.f ⊗ₘ X.p
    rw [MonoidalPreadditive.add_tensor]

variable [CategoryTheory.Linear ℂ C] [MonoidalLinear ℂ C]

/-- And so does monoidal linearity. -/
instance karoubiMonoidalLinear :
    MonoidalLinear ℂ (Karoubi C) where
  whiskerLeft_smul := by
    intro X Y Z c g
    apply Karoubi.hom_ext
    show X.p ⊗ₘ (c • g.f) = c • (X.p ⊗ₘ g.f)
    rw [tensorHom_def, tensorHom_def,
      MonoidalLinear.whiskerLeft_smul,
      CategoryTheory.Linear.comp_smul]
  smul_whiskerRight := by
    intro c X Y g Z
    apply Karoubi.hom_ext
    show (c • g.f) ⊗ₘ Z.p = c • (g.f ⊗ₘ Z.p)
    rw [tensorHom_def, tensorHom_def,
      MonoidalLinear.smul_whiskerRight,
      CategoryTheory.Linear.smul_comp]

end KaroubiLift

/-! ### The matrix lift -/

section MatLift

variable (C : Type*) [Category C] [Preadditive C]
  [MonoidalCategory C] [MonoidalPreadditive C]

/-- Monoidal preadditivity lifts to the matrix layer entrywise. -/
instance matMonoidalPreadditive :
    MonoidalPreadditive (Mat_ C) where
  whiskerLeft_zero := by
    intro X Y Z
    apply Mat_.hom_ext
    intro ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
    show (𝟙 X : Mat_.Hom X X) i₁ j₁ ⊗ₘ
      (0 : Y ⟶ Z) i₂ j₂ = _
    rw [show (0 : Y ⟶ Z) i₂ j₂ = 0 from rfl,
      MonoidalPreadditive.tensor_zero]
    rfl
  zero_whiskerRight := by
    intro X Y Z
    apply Mat_.hom_ext
    intro ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
    show (0 : Y ⟶ Z) i₁ j₁ ⊗ₘ
      (𝟙 X : Mat_.Hom X X) i₂ j₂ = _
    rw [show (0 : Y ⟶ Z) i₁ j₁ = 0 from rfl,
      MonoidalPreadditive.zero_tensor]
    rfl
  whiskerLeft_add := by
    intro X Y Z g g'
    apply Mat_.hom_ext
    intro i j
    show (𝟙 X : Mat_.Hom X X) i.1 j.1 ⊗ₘ
      (g + g' : Mat_.Hom Y Z) i.2 j.2 = _
    rw [show (g + g' : Mat_.Hom Y Z) i.2 j.2 =
      g i.2 j.2 + g' i.2 j.2 from rfl,
      MonoidalPreadditive.tensor_add]
    rfl
  add_whiskerRight := by
    intro X Y Z g g'
    apply Mat_.hom_ext
    intro ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
    show (g + g' : Mat_.Hom Y Z) i₁ j₁ ⊗ₘ
      (𝟙 X : Mat_.Hom X X) i₂ j₂ = _
    rw [show (g + g' : Mat_.Hom Y Z) i₁ j₁ =
      g i₁ j₁ + g' i₁ j₁ from rfl,
      MonoidalPreadditive.add_tensor]
    rfl

variable [CategoryTheory.Linear ℂ C] [MonoidalLinear ℂ C]

/-- The entrywise linear structure on matrix Homs (general
base). -/
noncomputable instance matHomSMul' (M N : Mat_ C) :
    SMul ℂ (M ⟶ N) where
  smul c φ := fun i j => c • φ i j

/-- The matrix layer's hom-sets are ℂ-modules, entrywise. -/
noncomputable instance matHomModule' (M N : Mat_ C) :
    Module ℂ (M ⟶ N) where
  one_smul φ := by funext i j; exact one_smul ℂ (φ i j)
  mul_smul c d φ := by funext i j; exact mul_smul c d (φ i j)
  smul_zero c := by funext i j; exact smul_zero c
  smul_add c φ ψ := by
    funext i j
    show c • (φ i j + ψ i j) = c • φ i j + c • ψ i j
    exact smul_add c _ _
  add_smul c d φ := by
    funext i j
    show (c + d) • φ i j = c • φ i j + d • φ i j
    exact add_smul c d _
  zero_smul φ := by funext i j; exact zero_smul ℂ (φ i j)

/-- Hence the matrix layer is ℂ-linear. -/
noncomputable instance matLinear' :
    CategoryTheory.Linear ℂ (Mat_ C) where
  smul_comp M N K c φ ψ := by
    funext i k
    show ∑ j, (c • φ i j) ≫ ψ j k = c • ∑ j, φ i j ≫ ψ j k
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [CategoryTheory.Linear.smul_comp]
  comp_smul M N K φ c ψ := by
    funext i k
    show ∑ j, φ i j ≫ (c • ψ j k) = c • ∑ j, φ i j ≫ ψ j k
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [CategoryTheory.Linear.comp_smul]

private theorem base_tensor_smul {W X Y Z : C}
    (a : W ⟶ X) (c : ℂ) (b : Y ⟶ Z) :
    a ⊗ₘ (c • b) = c • (a ⊗ₘ b) := by
  rw [tensorHom_def, tensorHom_def,
    MonoidalLinear.whiskerLeft_smul,
    CategoryTheory.Linear.comp_smul]

private theorem base_smul_tensor {W X Y Z : C}
    (c : ℂ) (a : W ⟶ X) (b : Y ⟶ Z) :
    (c • a) ⊗ₘ b = c • (a ⊗ₘ b) := by
  rw [tensorHom_def, tensorHom_def,
    MonoidalLinear.smul_whiskerRight,
    CategoryTheory.Linear.smul_comp]

/-- And monoidal-linear, completing the instance chain for the
envelope. -/
instance matMonoidalLinear : MonoidalLinear ℂ (Mat_ C) where
  whiskerLeft_smul := by
    intro X Y Z c g
    apply Mat_.hom_ext
    intro i j
    show (𝟙 X : Mat_.Hom X X) i.1 j.1 ⊗ₘ
        (c • g i.2 j.2) =
      c • ((𝟙 X : Mat_.Hom X X) i.1 j.1 ⊗ₘ g i.2 j.2)
    exact base_tensor_smul C _ c _
  smul_whiskerRight := by
    intro c X Y g Z
    apply Mat_.hom_ext
    intro i j
    show (c • g i.1 j.1) ⊗ₘ
        (𝟙 Z : Mat_.Hom Z Z) i.2 j.2 =
      c • (g i.1 j.1 ⊗ₘ (𝟙 Z : Mat_.Hom Z Z) i.2 j.2)
    exact base_smul_tensor C c _ _

end MatLift

/-! ### The envelope chain -/

noncomputable example : MonoidalCategory (Env f) :=
  inferInstance

noncomputable example : MonoidalPreadditive (Env f) :=
  inferInstance

noncomputable example : MonoidalLinear ℂ (Env f) :=
  inferInstance

end RS
