import RS.Common.MathlibDeps

/-!
# The symmetric monoidal category of super vector spaces

The category **SuperVect** of finite-dimensional ℤ/2-graded complex
vector spaces with grading-preserving linear maps, equipped with a
monoidal structure whose tensor product respects the grading and
whose braiding carries the *Koszul sign*: the block exchanging
`V.odd ⊗ W.odd` into `W.odd ⊗ V.odd` acquires a factor of −1.
This is the target category of the fibre functor in the
Regts–Sevenster development.
-/

noncomputable section

namespace RS

open CategoryTheory
open scoped TensorProduct

/-! ### Objects and morphisms -/

/-- A *super vector space* over ℂ: a pair of finite-dimensional
complex vector spaces, called the *even* and *odd* components. -/
structure SuperVect where
  /-- The even-graded component. -/
  even : Type
  /-- The odd-graded component. -/
  odd : Type
  [evenAddCommGroup : AddCommGroup even]
  [evenModule : Module ℂ even]
  [oddAddCommGroup : AddCommGroup odd]
  [oddModule : Module ℂ odd]
  [evenFinite : FiniteDimensional ℂ even]
  [oddFinite : FiniteDimensional ℂ odd]

attribute [instance] SuperVect.evenAddCommGroup SuperVect.evenModule
  SuperVect.oddAddCommGroup SuperVect.oddModule
  SuperVect.evenFinite SuperVect.oddFinite

namespace SuperVect

/-- A morphism of super vector spaces: a pair of ℂ-linear maps
preserving the grading. -/
@[ext]
structure Hom (V W : SuperVect) where
  /-- The even component of the morphism. -/
  evenMap : V.even →ₗ[ℂ] W.even
  /-- The odd component of the morphism. -/
  oddMap : V.odd →ₗ[ℂ] W.odd

/-- The identity morphism on a super vector space. -/
@[simp]
def Hom.id (V : SuperVect) : Hom V V where
  evenMap := LinearMap.id
  oddMap := LinearMap.id

/-- Composition of super-vector-space morphisms. -/
@[simp]
def Hom.comp {V W X : SuperVect} (g : Hom W X) (f : Hom V W) : Hom V X where
  evenMap := g.evenMap.comp f.evenMap
  oddMap := g.oddMap.comp f.oddMap

/-- Super vector spaces and grading-preserving maps form a
category. -/
instance instCategoryStruct : CategoryStruct SuperVect where
  Hom := Hom
  id := Hom.id
  comp f g := Hom.comp g f

/-- Two morphisms agreeing in both components are equal. -/
@[ext]
theorem hom_ext {V W : SuperVect} {f g : V ⟶ W}
    (he : (f : Hom V W).evenMap = (g : Hom V W).evenMap)
    (ho : (f : Hom V W).oddMap = (g : Hom V W).oddMap) : f = g :=
  Hom.ext he ho

/-- SuperVect forms a category with grading-preserving linear maps. -/
instance instCategory : Category SuperVect where
  id_comp _ := by ext <;> simp [CategoryStruct.comp, CategoryStruct.id]
  comp_id _ := by ext <;> simp [CategoryStruct.comp, CategoryStruct.id]
  assoc _ _ _ := by ext <;> simp [CategoryStruct.comp]

/-! ### Tensor product -/

/-- The graded tensor product of two super vector spaces.  The even
component is `(V.even ⊗ W.even) × (V.odd ⊗ W.odd)` and the odd
component is `(V.even ⊗ W.odd) × (V.odd ⊗ W.even)`. -/
def tensorObj (V W : SuperVect) : SuperVect where
  even := (V.even ⊗[ℂ] W.even) × (V.odd ⊗[ℂ] W.odd)
  odd := (V.even ⊗[ℂ] W.odd) × (V.odd ⊗[ℂ] W.even)

/-- The tensor product of two grading-preserving maps acts
component-wise on each tensor block. -/
def tensorHom {V₁ V₂ W₁ W₂ : SuperVect}
    (f : Hom V₁ V₂) (g : Hom W₁ W₂) :
    Hom (tensorObj V₁ W₁) (tensorObj V₂ W₂) := by
  refine ⟨?_, ?_⟩
  · change (V₁.even ⊗[ℂ] W₁.even) × (V₁.odd ⊗[ℂ] W₁.odd) →ₗ[ℂ]
           (V₂.even ⊗[ℂ] W₂.even) × (V₂.odd ⊗[ℂ] W₂.odd)
    exact LinearMap.prodMap
      (TensorProduct.map f.evenMap g.evenMap)
      (TensorProduct.map f.oddMap g.oddMap)
  · change (V₁.even ⊗[ℂ] W₁.odd) × (V₁.odd ⊗[ℂ] W₁.even) →ₗ[ℂ]
           (V₂.even ⊗[ℂ] W₂.odd) × (V₂.odd ⊗[ℂ] W₂.even)
    exact LinearMap.prodMap
      (TensorProduct.map f.evenMap g.oddMap)
      (TensorProduct.map f.oddMap g.evenMap)

/-- The monoidal unit: ℂ in even degree, the zero module in odd
degree.  Marked reducible so that `tensorUnit.odd` reduces to `PUnit`
during type-class synthesis. -/
@[reducible]
def tensorUnit : SuperVect where
  even := ℂ
  odd := PUnit

/-! ### The Koszul braiding -/

/-- Module-level even Koszul block: `TensorProduct.comm` on the
first factor and *minus* `TensorProduct.comm` on the second.
Stated over bare modules so that instances of it at compound
objects have syntactically reduced types. -/
def koszulEvenAux (A B C D : Type*)
    [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    [AddCommGroup C] [Module ℂ C] [AddCommGroup D] [Module ℂ D] :
    ((A ⊗[ℂ] B) × (C ⊗[ℂ] D)) →ₗ[ℂ] ((B ⊗[ℂ] A) × (D ⊗[ℂ] C)) :=
  LinearMap.prodMap
    (TensorProduct.comm ℂ A B).toLinearMap
    (-(TensorProduct.comm ℂ C D).toLinearMap)

/-- Module-level odd Koszul block: swaps the two summands and
applies `TensorProduct.comm` on each (no sign). -/
def koszulOddAux (A B C D : Type*)
    [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    [AddCommGroup C] [Module ℂ C] [AddCommGroup D] [Module ℂ D] :
    ((A ⊗[ℂ] B) × (C ⊗[ℂ] D)) →ₗ[ℂ] ((D ⊗[ℂ] C) × (B ⊗[ℂ] A)) :=
  LinearMap.prod
    ((TensorProduct.comm ℂ C D).toLinearMap.comp (LinearMap.snd ℂ _ _))
    ((TensorProduct.comm ℂ A B).toLinearMap.comp (LinearMap.fst ℂ _ _))

/-- The even component of the Koszul braiding: applies
`TensorProduct.comm` on the even⊗even block and
*minus* `TensorProduct.comm` on the odd⊗odd block. -/
def koszulBraidingEven (V W : SuperVect) :
    (V.even ⊗[ℂ] W.even) × (V.odd ⊗[ℂ] W.odd) →ₗ[ℂ]
    (W.even ⊗[ℂ] V.even) × (W.odd ⊗[ℂ] V.odd) :=
  koszulEvenAux V.even W.even V.odd W.odd

/-- The odd component of the Koszul braiding: swaps the two
blocks and applies `TensorProduct.comm` on each (no sign,
since even⊗odd and odd⊗even contribute (−1)^(0·1) = 1). -/
def koszulBraidingOdd (V W : SuperVect) :
    (V.even ⊗[ℂ] W.odd) × (V.odd ⊗[ℂ] W.even) →ₗ[ℂ]
    (W.even ⊗[ℂ] V.odd) × (W.odd ⊗[ℂ] V.even) :=
  koszulOddAux V.even W.odd V.odd W.even

/-- The Koszul braiding morphism `V ⊗ W → W ⊗ V` in SuperVect,
carrying the sign (−1)^(p·q) on the swap of homogeneous elements
of parity p and q. -/
def koszulBraiding (V W : SuperVect) :
    Hom (tensorObj V W) (tensorObj W V) := by
  refine ⟨?_, ?_⟩
  · change (V.even ⊗[ℂ] W.even) × (V.odd ⊗[ℂ] W.odd) →ₗ[ℂ]
           (W.even ⊗[ℂ] V.even) × (W.odd ⊗[ℂ] V.odd)
    exact koszulBraidingEven V W
  · change (V.even ⊗[ℂ] W.odd) × (V.odd ⊗[ℂ] W.even) →ₗ[ℂ]
           (W.even ⊗[ℂ] V.odd) × (W.odd ⊗[ℂ] V.even)
    exact koszulBraidingOdd V W

/-- The Koszul braiding is a self-inverse: the two applications of
the sign on the odd⊗odd block cancel, and the component swaps on
the odd part compose to the identity. -/
theorem koszulBraiding_self_inverse (V W : SuperVect) :
    Hom.comp (koszulBraiding W V) (koszulBraiding V W) = Hom.id (tensorObj V W)
      := by
  apply Hom.ext
  · -- Even component: comm ∘ comm = id, (-comm) ∘ (-comm) = comm ∘ comm = id
    change (koszulBraidingEven W V).comp (koszulBraidingEven V W) = LinearMap.id
    apply LinearMap.ext; intro ⟨x, y⟩
    simp only [koszulBraidingEven, koszulEvenAux, LinearMap.comp_apply,
      LinearMap.prodMap_apply,
      LinearMap.neg_apply, LinearMap.id_apply, map_neg, neg_neg,
      LinearEquiv.coe_toLinearMap, TensorProduct.comm_comm]
  · -- Odd component: swap ∘ swap = id, comm ∘ comm = id
    change (koszulBraidingOdd W V).comp (koszulBraidingOdd V W) = LinearMap.id
    apply LinearMap.ext; intro ⟨x, y⟩
    simp only [koszulBraidingOdd, koszulOddAux, LinearMap.comp_apply,
      LinearMap.prod_apply,
      LinearMap.snd_apply, LinearMap.fst_apply, LinearMap.id_apply,
        Function.prod,
      LinearEquiv.coe_toLinearMap, TensorProduct.comm_comm]

/-- Application of the Koszul odd braiding to a pair of elements. -/
@[simp]
private theorem koszulBraidingOdd_pair (V W : SuperVect)
    (x : V.even ⊗[ℂ] W.odd) (y : V.odd ⊗[ℂ] W.even) :
    koszulBraidingOdd V W ⟨x, y⟩ =
    ⟨(TensorProduct.comm ℂ V.odd W.even) y,
     (TensorProduct.comm ℂ V.even W.odd) x⟩ := rfl

/-! ### Koszul braiding as a categorical isomorphism -/

/-- The Koszul braiding as an isomorphism in SuperVect. -/
def koszulBraidingIso (V W : SuperVect) :
    tensorObj V W ≅ tensorObj W V where
  hom := koszulBraiding V W
  inv := koszulBraiding W V
  hom_inv_id := koszulBraiding_self_inverse V W
  inv_hom_id := koszulBraiding_self_inverse W V

/-! ### Left and right unitors -/

/-- The left unitor isomorphism `𝟙_ ⊗ V ≅ V`. -/
def leftUnitor (V : SuperVect) :
    tensorObj tensorUnit V ≅ V where
  hom := by
    refine ⟨?_, ?_⟩
    · change (ℂ ⊗[ℂ] V.even) × (PUnit ⊗[ℂ] V.odd) →ₗ[ℂ] V.even
      exact (TensorProduct.lid ℂ V.even).toLinearMap.comp (LinearMap.fst ℂ _ _)
    · change (ℂ ⊗[ℂ] V.odd) × (PUnit ⊗[ℂ] V.even) →ₗ[ℂ] V.odd
      exact (TensorProduct.lid ℂ V.odd).toLinearMap.comp (LinearMap.fst ℂ _ _)
  inv := by
    refine ⟨?_, ?_⟩
    · change V.even →ₗ[ℂ] (ℂ ⊗[ℂ] V.even) × (PUnit ⊗[ℂ] V.odd)
      exact LinearMap.inl ℂ _ _ ∘ₗ (TensorProduct.lid ℂ V.even).symm.toLinearMap
    · change V.odd →ₗ[ℂ] (ℂ ⊗[ℂ] V.odd) × (PUnit ⊗[ℂ] V.even)
      exact LinearMap.inl ℂ _ _ ∘ₗ (TensorProduct.lid ℂ V.odd).symm.toLinearMap
  hom_inv_id := by
    apply Hom.ext
    · change ((LinearMap.inl ℂ _ _ ∘ₗ (TensorProduct.lid ℂ
      V.even).symm.toLinearMap).comp
        ((TensorProduct.lid ℂ V.even).toLinearMap.comp (LinearMap.fst ℂ _ _))) =
          LinearMap.id
      apply LinearMap.ext; intro ⟨x, y⟩
      simp [Subsingleton.elim y 0]
    · change ((LinearMap.inl ℂ _ _ ∘ₗ (TensorProduct.lid ℂ
      V.odd).symm.toLinearMap).comp
        ((TensorProduct.lid ℂ V.odd).toLinearMap.comp (LinearMap.fst ℂ _ _))) =
          LinearMap.id
      apply LinearMap.ext; intro ⟨x, y⟩
      simp [Subsingleton.elim y 0]
  inv_hom_id := by
    apply Hom.ext
    · change ((TensorProduct.lid ℂ V.even).toLinearMap.comp (LinearMap.fst ℂ _
      _)).comp
        (LinearMap.inl ℂ _ _ ∘ₗ (TensorProduct.lid ℂ V.even).symm.toLinearMap) =
          LinearMap.id
      apply LinearMap.ext; intro x; simp
    · change ((TensorProduct.lid ℂ V.odd).toLinearMap.comp (LinearMap.fst ℂ _
      _)).comp
        (LinearMap.inl ℂ _ _ ∘ₗ (TensorProduct.lid ℂ V.odd).symm.toLinearMap) =
          LinearMap.id
      apply LinearMap.ext; intro x; simp

/-- The right unitor isomorphism `V ⊗ 𝟙_ ≅ V`. -/
def rightUnitor (V : SuperVect) :
    tensorObj V tensorUnit ≅ V where
  hom := by
    refine ⟨?_, ?_⟩
    · change (V.even ⊗[ℂ] ℂ) × (V.odd ⊗[ℂ] PUnit) →ₗ[ℂ] V.even
      exact (TensorProduct.rid ℂ V.even).toLinearMap.comp (LinearMap.fst ℂ _ _)
    · change (V.even ⊗[ℂ] PUnit) × (V.odd ⊗[ℂ] ℂ) →ₗ[ℂ] V.odd
      exact (TensorProduct.rid ℂ V.odd).toLinearMap.comp (LinearMap.snd ℂ _ _)
  inv := by
    refine ⟨?_, ?_⟩
    · change V.even →ₗ[ℂ] (V.even ⊗[ℂ] ℂ) × (V.odd ⊗[ℂ] PUnit)
      exact LinearMap.inl ℂ _ _ ∘ₗ (TensorProduct.rid ℂ V.even).symm.toLinearMap
    · change V.odd →ₗ[ℂ] (V.even ⊗[ℂ] PUnit) × (V.odd ⊗[ℂ] ℂ)
      exact LinearMap.inr ℂ _ _ ∘ₗ (TensorProduct.rid ℂ V.odd).symm.toLinearMap
  hom_inv_id := by
    apply Hom.ext
    · change ((LinearMap.inl ℂ _ _ ∘ₗ (TensorProduct.rid ℂ
      V.even).symm.toLinearMap).comp
        ((TensorProduct.rid ℂ V.even).toLinearMap.comp (LinearMap.fst ℂ _ _))) =
          LinearMap.id
      apply LinearMap.ext; intro ⟨x, y⟩
      simp [Subsingleton.elim y 0]
    · change ((LinearMap.inr ℂ _ _ ∘ₗ (TensorProduct.rid ℂ
      V.odd).symm.toLinearMap).comp
        ((TensorProduct.rid ℂ V.odd).toLinearMap.comp (LinearMap.snd ℂ _ _))) =
          LinearMap.id
      apply LinearMap.ext; intro ⟨x, y⟩
      simp [Subsingleton.elim x 0]
  inv_hom_id := by
    apply Hom.ext
    · change ((TensorProduct.rid ℂ V.even).toLinearMap.comp (LinearMap.fst ℂ _
      _)).comp
        (LinearMap.inl ℂ _ _ ∘ₗ (TensorProduct.rid ℂ V.even).symm.toLinearMap) =
          LinearMap.id
      apply LinearMap.ext; intro x; simp
    · change ((TensorProduct.rid ℂ V.odd).toLinearMap.comp (LinearMap.snd ℂ _
      _)).comp
        (LinearMap.inr ℂ _ _ ∘ₗ (TensorProduct.rid ℂ V.odd).symm.toLinearMap) =
          LinearMap.id
      apply LinearMap.ext; intro x; simp

/-! ### Associator -/

/-- Permutation of product components used in the associator:
`((A × B) × (C × D)) ≃ₗ ((A × C) × (D × B))`.  The mapping is
`(a, b, c, d) ↦ (a, c, d, b)`.  All field proofs hold by `rfl`
because the permutation is a definitional reshuffling of product
components. -/
private def prod4Perm (A B C D : Type*)
    [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    [AddCommGroup C] [Module ℂ C] [AddCommGroup D] [Module ℂ D] :
    ((A × B) × (C × D)) ≃ₗ[ℂ] ((A × C) × (D × B)) :=
  { toFun := fun ⟨⟨a, b⟩, ⟨c, d⟩⟩ => ⟨⟨a, c⟩, ⟨d, b⟩⟩
    map_add' := fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ ⟨⟨_, _⟩, ⟨_, _⟩⟩ => rfl
    map_smul' := fun _ ⟨⟨_, _⟩, ⟨_, _⟩⟩ => rfl
    invFun := fun ⟨⟨a, c⟩, ⟨d, b⟩⟩ => ⟨⟨a, b⟩, ⟨c, d⟩⟩
    left_inv := fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ => rfl
    right_inv := fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ => rfl }

/-- Module-level associator block.  The construction distributes
the tensor over products (via `prodLeft` and `prodRight`),
reassociates each tensor block (via `TensorProduct.assoc`), and
permutes the four summands via `prod4Perm`.  Stated over bare
modules so that instances of it at compound objects have
syntactically reduced types; the even and odd components of the
SuperVect associator are its instantiations with the two `C`-slots
in the two orders. -/
def assocAux (A₁ A₂ B₁ B₂ C₁ C₂ : Type*)
    [AddCommGroup A₁] [Module ℂ A₁] [AddCommGroup A₂] [Module ℂ A₂]
    [AddCommGroup B₁] [Module ℂ B₁] [AddCommGroup B₂] [Module ℂ B₂]
    [AddCommGroup C₁] [Module ℂ C₁] [AddCommGroup C₂] [Module ℂ C₂] :
    ((((A₁ ⊗[ℂ] B₁) × (A₂ ⊗[ℂ] B₂)) ⊗[ℂ] C₁) ×
    (((A₁ ⊗[ℂ] B₂) × (A₂ ⊗[ℂ] B₁)) ⊗[ℂ] C₂)) ≃ₗ[ℂ]
    ((A₁ ⊗[ℂ] ((B₁ ⊗[ℂ] C₁) × (B₂ ⊗[ℂ] C₂))) ×
    (A₂ ⊗[ℂ] ((B₁ ⊗[ℂ] C₂) × (B₂ ⊗[ℂ] C₁)))) :=
  let s1 := LinearEquiv.prodCongr
    (TensorProduct.prodLeft ℂ ℂ (A₁ ⊗[ℂ] B₁) (A₂ ⊗[ℂ] B₂) C₁)
    (TensorProduct.prodLeft ℂ ℂ (A₁ ⊗[ℂ] B₂) (A₂ ⊗[ℂ] B₁) C₂)
  let s2 := prod4Perm
    ((A₁ ⊗[ℂ] B₁) ⊗[ℂ] C₁) ((A₂ ⊗[ℂ] B₂) ⊗[ℂ] C₁)
    ((A₁ ⊗[ℂ] B₂) ⊗[ℂ] C₂) ((A₂ ⊗[ℂ] B₁) ⊗[ℂ] C₂)
  let s3 := LinearEquiv.prodCongr
    (LinearEquiv.prodCongr (TensorProduct.assoc ℂ A₁ B₁ C₁)
      (TensorProduct.assoc ℂ A₁ B₂ C₂))
    (LinearEquiv.prodCongr (TensorProduct.assoc ℂ A₂ B₁ C₂)
      (TensorProduct.assoc ℂ A₂ B₂ C₁))
  let s4 := LinearEquiv.prodCongr
    (LinearEquiv.symm (TensorProduct.prodRight ℂ ℂ A₁
      (B₁ ⊗[ℂ] C₁) (B₂ ⊗[ℂ] C₂)))
    (LinearEquiv.symm (TensorProduct.prodRight ℂ ℂ A₂
      (B₁ ⊗[ℂ] C₂) (B₂ ⊗[ℂ] C₁)))
  s1 ≪≫ₗ s2 ≪≫ₗ s3 ≪≫ₗ s4

/-- The even component of the associator equivalence. -/
private def assocEvenEquiv (V W X : SuperVect) :
    ((((V.even ⊗[ℂ] W.even) × (V.odd ⊗[ℂ] W.odd)) ⊗[ℂ] X.even) ×
    (((V.even ⊗[ℂ] W.odd) × (V.odd ⊗[ℂ] W.even)) ⊗[ℂ] X.odd)) ≃ₗ[ℂ]
    ((V.even ⊗[ℂ] ((W.even ⊗[ℂ] X.even) × (W.odd ⊗[ℂ] X.odd))) ×
    (V.odd ⊗[ℂ] ((W.even ⊗[ℂ] X.odd) × (W.odd ⊗[ℂ] X.even)))) :=
  assocAux V.even V.odd W.even W.odd X.even X.odd

/-- The odd component of the associator equivalence: `assocAux`
with the roles of the two `X`-slots swapped. -/
private def assocOddEquiv (V W X : SuperVect) :
    ((((V.even ⊗[ℂ] W.even) × (V.odd ⊗[ℂ] W.odd)) ⊗[ℂ] X.odd) ×
    (((V.even ⊗[ℂ] W.odd) × (V.odd ⊗[ℂ] W.even)) ⊗[ℂ] X.even)) ≃ₗ[ℂ]
    ((V.even ⊗[ℂ] ((W.even ⊗[ℂ] X.odd) × (W.odd ⊗[ℂ] X.even))) ×
    (V.odd ⊗[ℂ] ((W.even ⊗[ℂ] X.even) × (W.odd ⊗[ℂ] X.odd)))) :=
  assocAux V.even V.odd W.even W.odd X.odd X.even

/-- The associator isomorphism `(V ⊗ W) ⊗ X ≅ V ⊗ (W ⊗ X)` in SuperVect.
Distributes tensor over products, reassociates each block, and
permutes the summands back into the canonical grading order. -/
def associator (V W X : SuperVect) :
    tensorObj (tensorObj V W) X ≅ tensorObj V (tensorObj W X) where
  hom := by
    refine ⟨?_, ?_⟩
    · change (((V.even ⊗[ℂ] W.even) × (V.odd ⊗[ℂ] W.odd)) ⊗[ℂ] X.even) ×
             (((V.even ⊗[ℂ] W.odd) × (V.odd ⊗[ℂ] W.even)) ⊗[ℂ] X.odd) →ₗ[ℂ]
             (V.even ⊗[ℂ] ((W.even ⊗[ℂ] X.even) × (W.odd ⊗[ℂ] X.odd))) ×
             (V.odd ⊗[ℂ] ((W.even ⊗[ℂ] X.odd) × (W.odd ⊗[ℂ] X.even)))
      exact LinearEquiv.toLinearMap (assocEvenEquiv V W X)
    · change (((V.even ⊗[ℂ] W.even) × (V.odd ⊗[ℂ] W.odd)) ⊗[ℂ] X.odd) ×
             (((V.even ⊗[ℂ] W.odd) × (V.odd ⊗[ℂ] W.even)) ⊗[ℂ] X.even) →ₗ[ℂ]
             (V.even ⊗[ℂ] ((W.even ⊗[ℂ] X.odd) × (W.odd ⊗[ℂ] X.even))) ×
             (V.odd ⊗[ℂ] ((W.even ⊗[ℂ] X.even) × (W.odd ⊗[ℂ] X.odd)))
      exact LinearEquiv.toLinearMap (assocOddEquiv V W X)
  inv := by
    refine ⟨?_, ?_⟩
    · change (V.even ⊗[ℂ] ((W.even ⊗[ℂ] X.even) × (W.odd ⊗[ℂ] X.odd))) ×
             (V.odd ⊗[ℂ] ((W.even ⊗[ℂ] X.odd) × (W.odd ⊗[ℂ] X.even))) →ₗ[ℂ]
             (((V.even ⊗[ℂ] W.even) × (V.odd ⊗[ℂ] W.odd)) ⊗[ℂ] X.even) ×
             (((V.even ⊗[ℂ] W.odd) × (V.odd ⊗[ℂ] W.even)) ⊗[ℂ] X.odd)
      exact LinearEquiv.toLinearMap (LinearEquiv.symm (assocEvenEquiv V W X))
    · change (V.even ⊗[ℂ] ((W.even ⊗[ℂ] X.odd) × (W.odd ⊗[ℂ] X.even))) ×
             (V.odd ⊗[ℂ] ((W.even ⊗[ℂ] X.even) × (W.odd ⊗[ℂ] X.odd))) →ₗ[ℂ]
             (((V.even ⊗[ℂ] W.even) × (V.odd ⊗[ℂ] W.odd)) ⊗[ℂ] X.odd) ×
             (((V.even ⊗[ℂ] W.odd) × (V.odd ⊗[ℂ] W.even)) ⊗[ℂ] X.even)
      exact LinearEquiv.toLinearMap (LinearEquiv.symm (assocOddEquiv V W X))
  hom_inv_id := by
    apply Hom.ext <;> {
      apply LinearMap.ext; intro x
      simp only [CategoryStruct.comp, CategoryStruct.id, Hom.comp, Hom.id,
        LinearMap.comp_apply, LinearMap.id_apply]
      exact LinearEquiv.symm_apply_apply _ x }
  inv_hom_id := by
    apply Hom.ext <;> {
      apply LinearMap.ext; intro x
      simp only [CategoryStruct.comp, CategoryStruct.id, Hom.comp, Hom.id,
        LinearMap.comp_apply, LinearMap.id_apply]
      exact LinearEquiv.apply_symm_apply _ x }

/-! ### Associator computation lemmas -/

@[simp]
private lemma prod_fst_zero {A B : Type*} [Zero A] [Zero B] :
    (0 : A × B).1 = 0 := rfl

@[simp]
private lemma prod_snd_zero {A B : Type*} [Zero A] [Zero B] :
    (0 : A × B).2 = 0 := rfl

@[simp]
private lemma prod_mk_zero {A B : Type*} [Zero A] [Zero B] :
    ((0 : A), (0 : B)) = (0 : A × B) := rfl

@[simp]
private lemma prod4Perm_apply {A B C D : Type*}
    [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    [AddCommGroup C] [Module ℂ C] [AddCommGroup D] [Module ℂ D]
    (x : (A × B) × (C × D)) :
    prod4Perm A B C D x = ((x.1.1, x.2.1), (x.2.2, x.1.2)) := by
  obtain ⟨⟨a, b⟩, ⟨c, d⟩⟩ := x; rfl

private lemma prodRight_symm_tmul_fst {M₁ M₂ M₃ : Type*}
    [AddCommGroup M₁] [Module ℂ M₁]
    [AddCommGroup M₂] [Module ℂ M₂]
    [AddCommGroup M₃] [Module ℂ M₃]
    (m₁ : M₁) (m₂ : M₂) :
    (TensorProduct.prodRight ℂ ℂ M₁ M₂ M₃).symm (m₁ ⊗ₜ m₂, 0) =
      m₁ ⊗ₜ[ℂ] ((m₂, 0) : M₂ × M₃) := by
  apply (TensorProduct.prodRight ℂ ℂ M₁ M₂ M₃).injective
  simp [TensorProduct.prodRight_tmul]

private lemma prodRight_symm_tmul_snd {M₁ M₂ M₃ : Type*}
    [AddCommGroup M₁] [Module ℂ M₁]
    [AddCommGroup M₂] [Module ℂ M₂]
    [AddCommGroup M₃] [Module ℂ M₃]
    (m₁ : M₁) (m₃ : M₃) :
    (TensorProduct.prodRight ℂ ℂ M₁ M₂ M₃).symm (0, m₁ ⊗ₜ m₃) =
      m₁ ⊗ₜ[ℂ] ((0, m₃) : M₂ × M₃) := by
  apply (TensorProduct.prodRight ℂ ℂ M₁ M₂ M₃).injective
  simp [TensorProduct.prodRight_tmul]

-- Computation of `assocAux` on the four pure tensor generators.

/-- The associator block on a pure tensor of the `A₁ ⊗ B₁` summand
with `C₁`. -/
@[simp]
lemma assocAux_ee {A₁ A₂ B₁ B₂ C₁ C₂ : Type*}
    [AddCommGroup A₁] [Module ℂ A₁] [AddCommGroup A₂] [Module ℂ A₂]
    [AddCommGroup B₁] [Module ℂ B₁] [AddCommGroup B₂] [Module ℂ B₂]
    [AddCommGroup C₁] [Module ℂ C₁] [AddCommGroup C₂] [Module ℂ C₂]
    (a : A₁) (b : B₁) (c : C₁) :
    assocAux A₁ A₂ B₁ B₂ C₁ C₂
        (((a ⊗ₜ[ℂ] b, 0) ⊗ₜ[ℂ] c, 0) :
        ((((A₁ ⊗[ℂ] B₁) × (A₂ ⊗[ℂ] B₂)) ⊗[ℂ] C₁) ×
        (((A₁ ⊗[ℂ] B₂) × (A₂ ⊗[ℂ] B₁)) ⊗[ℂ] C₂))) =
      ((a ⊗ₜ[ℂ] ((b ⊗ₜ[ℂ] c, 0) : (B₁ ⊗[ℂ] C₁) × (B₂ ⊗[ℂ] C₂)), 0) :
        ((A₁ ⊗[ℂ] ((B₁ ⊗[ℂ] C₁) × (B₂ ⊗[ℂ] C₂))) ×
        (A₂ ⊗[ℂ] ((B₁ ⊗[ℂ] C₂) × (B₂ ⊗[ℂ] C₁))))) := by
  unfold assocAux
  simp only [LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply,
    prod_fst_zero, prod_snd_zero, prod_mk_zero, TensorProduct.prodLeft_tmul,
    TensorProduct.zero_tmul, map_zero, prod4Perm_apply,
    TensorProduct.assoc_tmul, prodRight_symm_tmul_fst]

/-- The associator block on a pure tensor of the `A₂ ⊗ B₂` summand
with `C₁`. -/
@[simp]
lemma assocAux_oo {A₁ A₂ B₁ B₂ C₁ C₂ : Type*}
    [AddCommGroup A₁] [Module ℂ A₁] [AddCommGroup A₂] [Module ℂ A₂]
    [AddCommGroup B₁] [Module ℂ B₁] [AddCommGroup B₂] [Module ℂ B₂]
    [AddCommGroup C₁] [Module ℂ C₁] [AddCommGroup C₂] [Module ℂ C₂]
    (p : A₂) (q : B₂) (c : C₁) :
    assocAux A₁ A₂ B₁ B₂ C₁ C₂
        ((((0 : A₁ ⊗[ℂ] B₁), p ⊗ₜ[ℂ] q) ⊗ₜ[ℂ] c, 0) :
        ((((A₁ ⊗[ℂ] B₁) × (A₂ ⊗[ℂ] B₂)) ⊗[ℂ] C₁) ×
        (((A₁ ⊗[ℂ] B₂) × (A₂ ⊗[ℂ] B₁)) ⊗[ℂ] C₂))) =
      (((0 : A₁ ⊗[ℂ] ((B₁ ⊗[ℂ] C₁) × (B₂ ⊗[ℂ] C₂))),
          p ⊗ₜ[ℂ] (((0 : B₁ ⊗[ℂ] C₂), q ⊗ₜ[ℂ] c) :
            (B₁ ⊗[ℂ] C₂) × (B₂ ⊗[ℂ] C₁))) :
        ((A₁ ⊗[ℂ] ((B₁ ⊗[ℂ] C₁) × (B₂ ⊗[ℂ] C₂))) ×
        (A₂ ⊗[ℂ] ((B₁ ⊗[ℂ] C₂) × (B₂ ⊗[ℂ] C₁))))) := by
  unfold assocAux
  simp only [LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply,
    prod_fst_zero, prod_snd_zero, prod_mk_zero, TensorProduct.prodLeft_tmul,
    TensorProduct.zero_tmul, map_zero, prod4Perm_apply,
    TensorProduct.assoc_tmul, prodRight_symm_tmul_snd]

/-- The associator block on a pure tensor of the `A₁ ⊗ B₂` summand
with `C₂`. -/
@[simp]
lemma assocAux_eo {A₁ A₂ B₁ B₂ C₁ C₂ : Type*}
    [AddCommGroup A₁] [Module ℂ A₁] [AddCommGroup A₂] [Module ℂ A₂]
    [AddCommGroup B₁] [Module ℂ B₁] [AddCommGroup B₂] [Module ℂ B₂]
    [AddCommGroup C₁] [Module ℂ C₁] [AddCommGroup C₂] [Module ℂ C₂]
    (a : A₁) (b : B₂) (c : C₂) :
    assocAux A₁ A₂ B₁ B₂ C₁ C₂
        (((0 : ((A₁ ⊗[ℂ] B₁) × (A₂ ⊗[ℂ] B₂)) ⊗[ℂ] C₁), (a ⊗ₜ[ℂ] b, 0) ⊗ₜ[ℂ] c) :
        ((((A₁ ⊗[ℂ] B₁) × (A₂ ⊗[ℂ] B₂)) ⊗[ℂ] C₁) ×
        (((A₁ ⊗[ℂ] B₂) × (A₂ ⊗[ℂ] B₁)) ⊗[ℂ] C₂))) =
      ((a ⊗ₜ[ℂ] (((0 : B₁ ⊗[ℂ] C₁), b ⊗ₜ[ℂ] c) : (B₁ ⊗[ℂ] C₁) × (B₂ ⊗[ℂ] C₂)),
        0) :
        ((A₁ ⊗[ℂ] ((B₁ ⊗[ℂ] C₁) × (B₂ ⊗[ℂ] C₂))) ×
        (A₂ ⊗[ℂ] ((B₁ ⊗[ℂ] C₂) × (B₂ ⊗[ℂ] C₁))))) := by
  unfold assocAux
  simp only [LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply,
    prod_fst_zero, prod_snd_zero, prod_mk_zero, TensorProduct.prodLeft_tmul,
    TensorProduct.zero_tmul, map_zero, prod4Perm_apply,
    TensorProduct.assoc_tmul, prodRight_symm_tmul_snd]

/-- The associator block on a pure tensor of the `A₂ ⊗ B₁` summand
with `C₂`. -/
@[simp]
lemma assocAux_oe {A₁ A₂ B₁ B₂ C₁ C₂ : Type*}
    [AddCommGroup A₁] [Module ℂ A₁] [AddCommGroup A₂] [Module ℂ A₂]
    [AddCommGroup B₁] [Module ℂ B₁] [AddCommGroup B₂] [Module ℂ B₂]
    [AddCommGroup C₁] [Module ℂ C₁] [AddCommGroup C₂] [Module ℂ C₂]
    (p : A₂) (q : B₁) (c : C₂) :
    assocAux A₁ A₂ B₁ B₂ C₁ C₂
        (((0 : ((A₁ ⊗[ℂ] B₁) × (A₂ ⊗[ℂ] B₂)) ⊗[ℂ] C₁), ((0 : A₁ ⊗[ℂ] B₂), p
          ⊗ₜ[ℂ] q) ⊗ₜ[ℂ] c) :
        ((((A₁ ⊗[ℂ] B₁) × (A₂ ⊗[ℂ] B₂)) ⊗[ℂ] C₁) ×
        (((A₁ ⊗[ℂ] B₂) × (A₂ ⊗[ℂ] B₁)) ⊗[ℂ] C₂))) =
      (((0 : A₁ ⊗[ℂ] ((B₁ ⊗[ℂ] C₁) × (B₂ ⊗[ℂ] C₂))),
          p ⊗ₜ[ℂ] ((q ⊗ₜ[ℂ] c, 0) :
            (B₁ ⊗[ℂ] C₂) × (B₂ ⊗[ℂ] C₁))) :
        ((A₁ ⊗[ℂ] ((B₁ ⊗[ℂ] C₁) × (B₂ ⊗[ℂ] C₂))) ×
        (A₂ ⊗[ℂ] ((B₁ ⊗[ℂ] C₂) × (B₂ ⊗[ℂ] C₁))))) := by
  unfold assocAux
  simp only [LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply,
    prod_fst_zero, prod_snd_zero, prod_mk_zero, TensorProduct.prodLeft_tmul,
    TensorProduct.zero_tmul, map_zero, prod4Perm_apply,
    TensorProduct.assoc_tmul, prodRight_symm_tmul_fst]

-- The inverse of `assocAux` on the image generators, by
-- `symm_apply_eq` from the forward lemmas.

/-- The inverse associator block on a pure tensor of `A₁` with the
`B₁ ⊗ C₁` summand. -/
@[simp]
lemma assocAux_symm_ee {A₁ A₂ B₁ B₂ C₁ C₂ : Type*}
    [AddCommGroup A₁] [Module ℂ A₁] [AddCommGroup A₂] [Module ℂ A₂]
    [AddCommGroup B₁] [Module ℂ B₁] [AddCommGroup B₂] [Module ℂ B₂]
    [AddCommGroup C₁] [Module ℂ C₁] [AddCommGroup C₂] [Module ℂ C₂]
    (a : A₁) (b : B₁) (c : C₁) :
    (assocAux A₁ A₂ B₁ B₂ C₁ C₂).symm
        ((a ⊗ₜ[ℂ] ((b ⊗ₜ[ℂ] c, 0) : (B₁ ⊗[ℂ] C₁) × (B₂ ⊗[ℂ] C₂)), 0) :
        ((A₁ ⊗[ℂ] ((B₁ ⊗[ℂ] C₁) × (B₂ ⊗[ℂ] C₂))) ×
        (A₂ ⊗[ℂ] ((B₁ ⊗[ℂ] C₂) × (B₂ ⊗[ℂ] C₁))))) =
      (((a ⊗ₜ[ℂ] b, 0) ⊗ₜ[ℂ] c, 0) :
        ((((A₁ ⊗[ℂ] B₁) × (A₂ ⊗[ℂ] B₂)) ⊗[ℂ] C₁) ×
        (((A₁ ⊗[ℂ] B₂) × (A₂ ⊗[ℂ] B₁)) ⊗[ℂ] C₂))) := by
  rw [LinearEquiv.symm_apply_eq, assocAux_ee]

/-- The inverse associator block on a pure tensor of `A₂` with the
`B₂ ⊗ C₁` summand. -/
@[simp]
lemma assocAux_symm_oo {A₁ A₂ B₁ B₂ C₁ C₂ : Type*}
    [AddCommGroup A₁] [Module ℂ A₁] [AddCommGroup A₂] [Module ℂ A₂]
    [AddCommGroup B₁] [Module ℂ B₁] [AddCommGroup B₂] [Module ℂ B₂]
    [AddCommGroup C₁] [Module ℂ C₁] [AddCommGroup C₂] [Module ℂ C₂]
    (p : A₂) (q : B₂) (c : C₁) :
    (assocAux A₁ A₂ B₁ B₂ C₁ C₂).symm
        (((0 : A₁ ⊗[ℂ] ((B₁ ⊗[ℂ] C₁) × (B₂ ⊗[ℂ] C₂))),
          p ⊗ₜ[ℂ] (((0 : B₁ ⊗[ℂ] C₂), q ⊗ₜ[ℂ] c) :
            (B₁ ⊗[ℂ] C₂) × (B₂ ⊗[ℂ] C₁))) :
        ((A₁ ⊗[ℂ] ((B₁ ⊗[ℂ] C₁) × (B₂ ⊗[ℂ] C₂))) ×
        (A₂ ⊗[ℂ] ((B₁ ⊗[ℂ] C₂) × (B₂ ⊗[ℂ] C₁))))) =
      ((((0 : A₁ ⊗[ℂ] B₁), p ⊗ₜ[ℂ] q) ⊗ₜ[ℂ] c, 0) :
        ((((A₁ ⊗[ℂ] B₁) × (A₂ ⊗[ℂ] B₂)) ⊗[ℂ] C₁) ×
        (((A₁ ⊗[ℂ] B₂) × (A₂ ⊗[ℂ] B₁)) ⊗[ℂ] C₂))) := by
  rw [LinearEquiv.symm_apply_eq, assocAux_oo]

/-- The inverse associator block on a pure tensor of `A₁` with the
`B₂ ⊗ C₂` summand. -/
@[simp]
lemma assocAux_symm_eo {A₁ A₂ B₁ B₂ C₁ C₂ : Type*}
    [AddCommGroup A₁] [Module ℂ A₁] [AddCommGroup A₂] [Module ℂ A₂]
    [AddCommGroup B₁] [Module ℂ B₁] [AddCommGroup B₂] [Module ℂ B₂]
    [AddCommGroup C₁] [Module ℂ C₁] [AddCommGroup C₂] [Module ℂ C₂]
    (a : A₁) (b : B₂) (c : C₂) :
    (assocAux A₁ A₂ B₁ B₂ C₁ C₂).symm
        ((a ⊗ₜ[ℂ] (((0 : B₁ ⊗[ℂ] C₁), b ⊗ₜ[ℂ] c) : (B₁ ⊗[ℂ] C₁) × (B₂ ⊗[ℂ] C₂)),
          0) :
        ((A₁ ⊗[ℂ] ((B₁ ⊗[ℂ] C₁) × (B₂ ⊗[ℂ] C₂))) ×
        (A₂ ⊗[ℂ] ((B₁ ⊗[ℂ] C₂) × (B₂ ⊗[ℂ] C₁))))) =
      (((0 : ((A₁ ⊗[ℂ] B₁) × (A₂ ⊗[ℂ] B₂)) ⊗[ℂ] C₁), (a ⊗ₜ[ℂ] b, 0) ⊗ₜ[ℂ] c) :
        ((((A₁ ⊗[ℂ] B₁) × (A₂ ⊗[ℂ] B₂)) ⊗[ℂ] C₁) ×
        (((A₁ ⊗[ℂ] B₂) × (A₂ ⊗[ℂ] B₁)) ⊗[ℂ] C₂))) := by
  rw [LinearEquiv.symm_apply_eq, assocAux_eo]

/-- The inverse associator block on a pure tensor of `A₂` with the
`B₁ ⊗ C₂` summand. -/
@[simp]
lemma assocAux_symm_oe {A₁ A₂ B₁ B₂ C₁ C₂ : Type*}
    [AddCommGroup A₁] [Module ℂ A₁] [AddCommGroup A₂] [Module ℂ A₂]
    [AddCommGroup B₁] [Module ℂ B₁] [AddCommGroup B₂] [Module ℂ B₂]
    [AddCommGroup C₁] [Module ℂ C₁] [AddCommGroup C₂] [Module ℂ C₂]
    (p : A₂) (q : B₁) (c : C₂) :
    (assocAux A₁ A₂ B₁ B₂ C₁ C₂).symm
        (((0 : A₁ ⊗[ℂ] ((B₁ ⊗[ℂ] C₁) × (B₂ ⊗[ℂ] C₂))),
          p ⊗ₜ[ℂ] ((q ⊗ₜ[ℂ] c, 0) :
            (B₁ ⊗[ℂ] C₂) × (B₂ ⊗[ℂ] C₁))) :
        ((A₁ ⊗[ℂ] ((B₁ ⊗[ℂ] C₁) × (B₂ ⊗[ℂ] C₂))) ×
        (A₂ ⊗[ℂ] ((B₁ ⊗[ℂ] C₂) × (B₂ ⊗[ℂ] C₁))))) =
      (((0 : ((A₁ ⊗[ℂ] B₁) × (A₂ ⊗[ℂ] B₂)) ⊗[ℂ] C₁), ((0 : A₁ ⊗[ℂ] B₂), p ⊗ₜ[ℂ]
        q) ⊗ₜ[ℂ] c) :
        ((((A₁ ⊗[ℂ] B₁) × (A₂ ⊗[ℂ] B₂)) ⊗[ℂ] C₁) ×
        (((A₁ ⊗[ℂ] B₂) × (A₂ ⊗[ℂ] B₁)) ⊗[ℂ] C₂))) := by
  rw [LinearEquiv.symm_apply_eq, assocAux_oe]

-- Computation of the Koszul blocks on the two generator shapes;
-- the sign of the even block is emitted outside the pair so the
-- associator computation lemmas can fire beneath it.
/-- The even Koszul block on the first summand: plain
commutation, no sign. -/
@[simp]
lemma koszulEvenAux_fst {A B C D : Type*}
    [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    [AddCommGroup C] [Module ℂ C] [AddCommGroup D] [Module ℂ D]
    (a : A) (b : B) :
    koszulEvenAux A B C D ((a ⊗ₜ[ℂ] b, 0) : (A ⊗[ℂ] B) × (C ⊗[ℂ] D)) =
      ((b ⊗ₜ[ℂ] a, 0) : (B ⊗[ℂ] A) × (D ⊗[ℂ] C)) := by
  simp [koszulEvenAux]

/-- **The Koszul sign**: on the second summand — the odd⊗odd
block — the even block commutes *and* negates. -/
@[simp]
lemma koszulEvenAux_snd {A B C D : Type*}
    [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    [AddCommGroup C] [Module ℂ C] [AddCommGroup D] [Module ℂ D]
    (c : C) (d : D) :
    koszulEvenAux A B C D ((0, c ⊗ₜ[ℂ] d) : (A ⊗[ℂ] B) × (C ⊗[ℂ] D)) =
      -(((0, d ⊗ₜ[ℂ] c)) : (B ⊗[ℂ] A) × (D ⊗[ℂ] C)) := by
  simp only [koszulEvenAux, LinearMap.prodMap_apply, map_zero,
    LinearMap.neg_apply, LinearEquiv.coe_toLinearMap,
    TensorProduct.comm_tmul]
  ext <;> simp

/-- The odd Koszul block on the first summand: commutation into
the other summand, no sign. -/
@[simp]
lemma koszulOddAux_fst {A B C D : Type*}
    [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    [AddCommGroup C] [Module ℂ C] [AddCommGroup D] [Module ℂ D]
    (a : A) (b : B) :
    koszulOddAux A B C D ((a ⊗ₜ[ℂ] b, 0) : (A ⊗[ℂ] B) × (C ⊗[ℂ] D)) =
      ((0, b ⊗ₜ[ℂ] a) : (D ⊗[ℂ] C) × (B ⊗[ℂ] A)) := by
  simp [koszulOddAux]

/-- The odd Koszul block on the second summand: likewise
unsigned — only the odd⊗odd block carries the sign. -/
@[simp]
lemma koszulOddAux_snd {A B C D : Type*}
    [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    [AddCommGroup C] [Module ℂ C] [AddCommGroup D] [Module ℂ D]
    (c : C) (d : D) :
    koszulOddAux A B C D ((0, c ⊗ₜ[ℂ] d) : (A ⊗[ℂ] B) × (C ⊗[ℂ] D)) =
      ((d ⊗ₜ[ℂ] c, 0) : (D ⊗[ℂ] C) × (B ⊗[ℂ] A)) := by
  simp [koszulOddAux]

-- Sign bookkeeping for the hexagon proofs: negations are kept
-- outside pairs (the `Prod.neg_mk` normal form is disabled there),
-- so single-sided negated pairs must re-assemble to negated pairs.
private lemma prod_mk_neg_left {A B : Type*}
    [AddCommGroup A] [AddCommGroup B] (u : A) :
    ((-u, (0 : B)) : A × B) = -(u, 0) := by
  ext <;> simp

private lemma prod_mk_neg_right {A B : Type*}
    [AddCommGroup A] [AddCommGroup B] (v : B) :
    (((0 : A), -v) : A × B) = -((0 : A), v) := by
  ext <;> simp

/-- The triangle coherence of the module-level associator block
against the unit slots `ℂ` (even) and `PUnit` (odd).  Both graded
components of the SuperVect triangle are instantiations. -/
private theorem assocAux_triangle
    (A₁ A₂ B₁ B₂ : Type*)
    [AddCommGroup A₁] [Module ℂ A₁] [AddCommGroup A₂] [Module ℂ A₂]
    [AddCommGroup B₁] [Module ℂ B₁] [AddCommGroup B₂] [Module ℂ B₂] :
    LinearMap.prodMap
        (TensorProduct.map LinearMap.id
          ((TensorProduct.lid ℂ B₁).toLinearMap ∘ₗ
            LinearMap.fst ℂ (ℂ ⊗[ℂ] B₁) (PUnit ⊗[ℂ] B₂)))
        (TensorProduct.map LinearMap.id
          ((TensorProduct.lid ℂ B₂).toLinearMap ∘ₗ
            LinearMap.fst ℂ (ℂ ⊗[ℂ] B₂) (PUnit ⊗[ℂ] B₁))) ∘ₗ
      (assocAux A₁ A₂ ℂ PUnit B₁ B₂).toLinearMap =
    LinearMap.prodMap
        (TensorProduct.map
          ((TensorProduct.rid ℂ A₁).toLinearMap ∘ₗ
            LinearMap.fst ℂ (A₁ ⊗[ℂ] ℂ) (A₂ ⊗[ℂ] PUnit)) LinearMap.id)
        (TensorProduct.map
          ((TensorProduct.rid ℂ A₂).toLinearMap ∘ₗ
            LinearMap.snd ℂ (A₁ ⊗[ℂ] PUnit) (A₂ ⊗[ℂ] ℂ)) LinearMap.id) := by
  ext x
  all_goals simp

/-- The forward hexagon for the even graded component, at the
module level: braiding past a tensor product in two steps agrees
with braiding past its factors. -/
private theorem koszulAux_hexagon_fwd_even
    (A₁ A₂ B₁ B₂ C₁ C₂ : Type*)
    [AddCommGroup A₁] [Module ℂ A₁] [AddCommGroup A₂] [Module ℂ A₂]
    [AddCommGroup B₁] [Module ℂ B₁] [AddCommGroup B₂] [Module ℂ B₂]
    [AddCommGroup C₁] [Module ℂ C₁] [AddCommGroup C₂] [Module ℂ C₂] :
    ((assocAux B₁ B₂ C₁ C₂ A₁ A₂).toLinearMap ∘ₗ
      koszulEvenAux A₁ ((B₁ ⊗[ℂ] C₁) × (B₂ ⊗[ℂ] C₂)) A₂ ((B₁ ⊗[ℂ] C₂) × (B₂ ⊗[ℂ]
        C₁))) ∘ₗ
    (assocAux A₁ A₂ B₁ B₂ C₁ C₂).toLinearMap =
    (LinearMap.prodMap
        (TensorProduct.map LinearMap.id (koszulEvenAux A₁ C₁ A₂ C₂))
        (TensorProduct.map LinearMap.id (koszulOddAux A₁ C₂ A₂ C₁)) ∘ₗ
      (assocAux B₁ B₂ A₁ A₂ C₁ C₂).toLinearMap) ∘ₗ
    LinearMap.prodMap
        (TensorProduct.map (koszulEvenAux A₁ B₁ A₂ B₂) LinearMap.id)
        (TensorProduct.map (koszulOddAux A₁ B₂ A₂ B₁) LinearMap.id) := by
  ext x
  all_goals simp [-Prod.neg_mk, TensorProduct.neg_tmul,
    TensorProduct.tmul_neg, prod_mk_neg_left, prod_mk_neg_right]

/-- The forward hexagon for the odd graded component. -/
private theorem koszulAux_hexagon_fwd_odd
    (A₁ A₂ B₁ B₂ C₁ C₂ : Type*)
    [AddCommGroup A₁] [Module ℂ A₁] [AddCommGroup A₂] [Module ℂ A₂]
    [AddCommGroup B₁] [Module ℂ B₁] [AddCommGroup B₂] [Module ℂ B₂]
    [AddCommGroup C₁] [Module ℂ C₁] [AddCommGroup C₂] [Module ℂ C₂] :
    ((assocAux B₁ B₂ C₁ C₂ A₂ A₁).toLinearMap ∘ₗ
      koszulOddAux A₁ ((B₁ ⊗[ℂ] C₂) × (B₂ ⊗[ℂ] C₁)) A₂ ((B₁ ⊗[ℂ] C₁) × (B₂ ⊗[ℂ]
        C₂))) ∘ₗ
    (assocAux A₁ A₂ B₁ B₂ C₂ C₁).toLinearMap =
    (LinearMap.prodMap
        (TensorProduct.map LinearMap.id (koszulOddAux A₁ C₂ A₂ C₁))
        (TensorProduct.map LinearMap.id (koszulEvenAux A₁ C₁ A₂ C₂)) ∘ₗ
      (assocAux B₁ B₂ A₁ A₂ C₂ C₁).toLinearMap) ∘ₗ
    LinearMap.prodMap
        (TensorProduct.map (koszulEvenAux A₁ B₁ A₂ B₂) LinearMap.id)
        (TensorProduct.map (koszulOddAux A₁ B₂ A₂ B₁) LinearMap.id) := by
  ext x
  all_goals simp [-Prod.neg_mk, TensorProduct.neg_tmul,
    TensorProduct.tmul_neg, prod_mk_neg_left]

/-- The reverse hexagon for the even graded component, phrased
through the inverse associator blocks. -/
private theorem koszulAux_hexagon_rev_even
    (A₁ A₂ B₁ B₂ C₁ C₂ : Type*)
    [AddCommGroup A₁] [Module ℂ A₁] [AddCommGroup A₂] [Module ℂ A₂]
    [AddCommGroup B₁] [Module ℂ B₁] [AddCommGroup B₂] [Module ℂ B₂]
    [AddCommGroup C₁] [Module ℂ C₁] [AddCommGroup C₂] [Module ℂ C₂] :
    ((assocAux C₁ C₂ A₁ A₂ B₁ B₂).symm.toLinearMap ∘ₗ
      koszulEvenAux ((A₁ ⊗[ℂ] B₁) × (A₂ ⊗[ℂ] B₂)) C₁ ((A₁ ⊗[ℂ] B₂) × (A₂ ⊗[ℂ]
        B₁)) C₂) ∘ₗ
    (assocAux A₁ A₂ B₁ B₂ C₁ C₂).symm.toLinearMap =
    (LinearMap.prodMap
        (TensorProduct.map (koszulEvenAux A₁ C₁ A₂ C₂) LinearMap.id)
        (TensorProduct.map (koszulOddAux A₁ C₂ A₂ C₁) LinearMap.id) ∘ₗ
      (assocAux A₁ A₂ C₁ C₂ B₁ B₂).symm.toLinearMap) ∘ₗ
    LinearMap.prodMap
        (TensorProduct.map LinearMap.id (koszulEvenAux B₁ C₁ B₂ C₂))
        (TensorProduct.map LinearMap.id (koszulOddAux B₁ C₂ B₂ C₁)) := by
  ext x
  all_goals simp [-Prod.neg_mk, TensorProduct.neg_tmul,
    TensorProduct.tmul_neg, prod_mk_neg_left, prod_mk_neg_right]

/-- The reverse hexagon for the odd graded component. -/
private theorem koszulAux_hexagon_rev_odd
    (A₁ A₂ B₁ B₂ C₁ C₂ : Type*)
    [AddCommGroup A₁] [Module ℂ A₁] [AddCommGroup A₂] [Module ℂ A₂]
    [AddCommGroup B₁] [Module ℂ B₁] [AddCommGroup B₂] [Module ℂ B₂]
    [AddCommGroup C₁] [Module ℂ C₁] [AddCommGroup C₂] [Module ℂ C₂] :
    ((assocAux C₁ C₂ A₁ A₂ B₂ B₁).symm.toLinearMap ∘ₗ
      koszulOddAux ((A₁ ⊗[ℂ] B₁) × (A₂ ⊗[ℂ] B₂)) C₂ ((A₁ ⊗[ℂ] B₂) × (A₂ ⊗[ℂ]
        B₁)) C₁) ∘ₗ
    (assocAux A₁ A₂ B₁ B₂ C₂ C₁).symm.toLinearMap =
    (LinearMap.prodMap
        (TensorProduct.map (koszulEvenAux A₁ C₁ A₂ C₂) LinearMap.id)
        (TensorProduct.map (koszulOddAux A₁ C₂ A₂ C₁) LinearMap.id) ∘ₗ
      (assocAux A₁ A₂ C₁ C₂ B₂ B₁).symm.toLinearMap) ∘ₗ
    LinearMap.prodMap
        (TensorProduct.map LinearMap.id (koszulOddAux B₁ C₂ B₂ C₁))
        (TensorProduct.map LinearMap.id (koszulEvenAux B₁ C₁ B₂ C₂)) := by
  ext x
  all_goals simp [-Prod.neg_mk, TensorProduct.neg_tmul,
    TensorProduct.tmul_neg, prod_mk_neg_right]

/-- The pentagon coherence of the module-level associator block:
both routes from a four-fold graded product to its right-nested
form agree.  Both graded components of the SuperVect pentagon are
instantiations. -/
private theorem assocAux_pentagon
    (A₁ A₂ B₁ B₂ C₁ C₂ D₁ D₂ : Type*)
    [AddCommGroup A₁] [Module ℂ A₁] [AddCommGroup A₂] [Module ℂ A₂]
    [AddCommGroup B₁] [Module ℂ B₁] [AddCommGroup B₂] [Module ℂ B₂]
    [AddCommGroup C₁] [Module ℂ C₁] [AddCommGroup C₂] [Module ℂ C₂]
    [AddCommGroup D₁] [Module ℂ D₁] [AddCommGroup D₂] [Module ℂ D₂] :
    (LinearMap.prodMap
        (TensorProduct.map LinearMap.id (assocAux B₁ B₂ C₁ C₂ D₁
          D₂).toLinearMap)
        (TensorProduct.map LinearMap.id (assocAux B₁ B₂ C₁ C₂ D₂
          D₁).toLinearMap) ∘ₗ
      (assocAux A₁ A₂ ((B₁ ⊗[ℂ] C₁) × (B₂ ⊗[ℂ] C₂))
        ((B₁ ⊗[ℂ] C₂) × (B₂ ⊗[ℂ] C₁)) D₁ D₂).toLinearMap) ∘ₗ
    LinearMap.prodMap
        (TensorProduct.map (assocAux A₁ A₂ B₁ B₂ C₁ C₂).toLinearMap
          LinearMap.id)
        (TensorProduct.map (assocAux A₁ A₂ B₁ B₂ C₂ C₁).toLinearMap
          LinearMap.id) =
    (assocAux A₁ A₂ B₁ B₂ ((C₁ ⊗[ℂ] D₁) × (C₂ ⊗[ℂ] D₂))
      ((C₁ ⊗[ℂ] D₂) × (C₂ ⊗[ℂ] D₁))).toLinearMap ∘ₗ
    (assocAux ((A₁ ⊗[ℂ] B₁) × (A₂ ⊗[ℂ] B₂))
      ((A₁ ⊗[ℂ] B₂) × (A₂ ⊗[ℂ] B₁)) C₁ C₂ D₁ D₂).toLinearMap := by
  ext x
  all_goals simp

/-! ### Component projection lemmas -/

@[simp]
private theorem cat_comp_evenMap {V W X : SuperVect} (f : V ⟶ W) (g : W ⟶ X) :
    (f ≫ g).evenMap = g.evenMap.comp f.evenMap := rfl

@[simp]
private theorem cat_comp_oddMap {V W X : SuperVect} (f : V ⟶ W) (g : W ⟶ X) :
    (f ≫ g).oddMap = g.oddMap.comp f.oddMap := rfl

@[simp]
private theorem cat_id_evenMap (V : SuperVect) :
    (𝟙 V : Hom V V).evenMap = LinearMap.id := rfl

@[simp]
private theorem cat_id_oddMap (V : SuperVect) :
    (𝟙 V : Hom V V).oddMap = LinearMap.id := rfl

/-- The even component of a tensor of morphisms: even⊗even and
odd⊗odd in parallel. -/
@[simp]
theorem tensorHom_evenMap {V₁ V₂ W₁ W₂ : SuperVect}
    (f : Hom V₁ V₂) (g : Hom W₁ W₂) :
    (tensorHom f g).evenMap = LinearMap.prodMap
      (TensorProduct.map f.evenMap g.evenMap)
      (TensorProduct.map f.oddMap g.oddMap) := rfl

/-- The odd component of a tensor of morphisms: even⊗odd and
odd⊗even in parallel. -/
@[simp]
theorem tensorHom_oddMap {V₁ V₂ W₁ W₂ : SuperVect}
    (f : Hom V₁ V₂) (g : Hom W₁ W₂) :
    (tensorHom f g).oddMap = LinearMap.prodMap
      (TensorProduct.map f.evenMap g.oddMap)
      (TensorProduct.map f.oddMap g.evenMap) := rfl

/-- The associator's even component is the even associator
equivalence. -/
@[simp]
theorem associator_hom_evenMap (V W X : SuperVect) :
    ((associator V W X).hom).evenMap =
      (assocEvenEquiv V W X).toLinearMap := rfl

/-- The associator's odd component is the odd associator
equivalence. -/
@[simp]
theorem associator_hom_oddMap (V W X : SuperVect) :
    ((associator V W X).hom).oddMap =
      (assocOddEquiv V W X).toLinearMap := rfl

/-- The inverse associator's even component. -/
@[simp]
theorem associator_inv_evenMap (V W X : SuperVect) :
    ((associator V W X).inv).evenMap =
      (assocEvenEquiv V W X).symm.toLinearMap := rfl

/-- The inverse associator's odd component. -/
@[simp]
theorem associator_inv_oddMap (V W X : SuperVect) :
    ((associator V W X).inv).oddMap =
      (assocOddEquiv V W X).symm.toLinearMap := rfl

/-- The left unitor's even component: the unit's odd part is zero,
so only the first summand survives. -/
@[simp]
theorem leftUnitor_hom_evenMap (V : SuperVect) :
    ((leftUnitor V).hom).evenMap =
      (TensorProduct.lid ℂ V.even).toLinearMap.comp (LinearMap.fst ℂ _ _) := rfl

/-- The left unitor's odd component. -/
@[simp]
theorem leftUnitor_hom_oddMap (V : SuperVect) :
    ((leftUnitor V).hom).oddMap =
      (TensorProduct.lid ℂ V.odd).toLinearMap.comp (LinearMap.fst ℂ _ _) := rfl

/-- The right unitor's even component. -/
@[simp]
theorem rightUnitor_hom_evenMap (V : SuperVect) :
    ((rightUnitor V).hom).evenMap =
      (TensorProduct.rid ℂ V.even).toLinearMap.comp (LinearMap.fst ℂ _ _) := rfl

/-- The right unitor's odd component: here it is the *second*
summand that survives, the unit sitting on the right. -/
@[simp]
theorem rightUnitor_hom_oddMap (V : SuperVect) :
    ((rightUnitor V).hom).oddMap =
      (TensorProduct.rid ℂ V.odd).toLinearMap.comp (LinearMap.snd ℂ _ _) := rfl

/-- The braiding's even component. -/
@[simp]
theorem koszulBraiding_evenMap (V W : SuperVect) :
    (koszulBraiding V W).evenMap = koszulBraidingEven V W := rfl

/-- The braiding's odd component. -/
@[simp]
theorem koszulBraiding_oddMap (V W : SuperVect) :
    (koszulBraiding V W).oddMap = koszulBraidingOdd V W := rfl

/-! ### Monoidal structure -/

/-- The monoidal category structure on SuperVect: graded tensor
product, ℂ unit, standard associator/unitors. -/
instance instMonoidalCategoryStruct : MonoidalCategoryStruct SuperVect where
  tensorObj := tensorObj
  whiskerLeft := fun (X : SuperVect) {Y₁ : SuperVect} {Y₂ : SuperVect}
    (f : Y₁ ⟶ Y₂) =>
    SuperVect.tensorHom (Hom.id X) f
  whiskerRight := fun {X₁ : SuperVect} {X₂ : SuperVect} (f : X₁ ⟶ X₂)
    (Y : SuperVect) =>
    SuperVect.tensorHom f (Hom.id Y)
  tensorHom := fun f g => SuperVect.tensorHom f g
  tensorUnit := tensorUnit
  associator := associator
  leftUnitor := leftUnitor
  rightUnitor := rightUnitor

/-! ### MonoidalCategory axioms -/

/-- `tensorHom id id = id`: the tensor of identity morphisms is
the identity on the tensor product. -/
private theorem tensorHom_id_id (X₁ X₂ : SuperVect) :
    SuperVect.tensorHom (Hom.id X₁) (Hom.id X₂) = Hom.id (tensorObj X₁ X₂) := by
  apply Hom.ext <;> {
    change LinearMap.prodMap
        (TensorProduct.map LinearMap.id LinearMap.id)
        (TensorProduct.map LinearMap.id LinearMap.id) = LinearMap.id
    simp [TensorProduct.map_id] }

/-- Composition distributes over tensor product of morphisms. -/
private theorem tensorHom_comp (X₁ Y₁ Z₁ X₂ Y₂ Z₂ : SuperVect)
    (f₁ : Hom X₁ Y₁) (f₂ : Hom X₂ Y₂)
    (g₁ : Hom Y₁ Z₁) (g₂ : Hom Y₂ Z₂) :
    Hom.comp (SuperVect.tensorHom g₁ g₂) (SuperVect.tensorHom f₁ f₂) =
    SuperVect.tensorHom (Hom.comp g₁ f₁) (Hom.comp g₂ f₂) := by
  apply Hom.ext <;> {
    change LinearMap.comp _ _ = _
    simp only [Hom.comp, SuperVect.tensorHom]
    change (LinearMap.prodMap _ _).comp (LinearMap.prodMap _ _) =
           LinearMap.prodMap _ _
    simp [LinearMap.prodMap_comp, TensorProduct.map_comp] }

/-- The full monoidal category structure on SuperVect, constructed
via `ofTensorHom`. -/
instance instMonoidalCategory : MonoidalCategory SuperVect :=
  MonoidalCategory.ofTensorHom
    (id_tensorHom_id := fun X₁ X₂ => tensorHom_id_id X₁ X₂)
    (id_tensorHom := fun _ {_ _} _ => rfl)
    (tensorHom_id := fun {_ _} _ _ => rfl)
    (tensorHom_comp_tensorHom := fun {_ _ _ _ _ _} f₁ f₂ g₁ g₂ => by
      show Hom.comp (SuperVect.tensorHom g₁ g₂) (SuperVect.tensorHom f₁ f₂) =
           SuperVect.tensorHom (Hom.comp g₁ f₁) (Hom.comp g₂ f₂)
      exact tensorHom_comp _ _ _ _ _ _ f₁ f₂ g₁ g₂)
    -- ═══════ ASSOCIATOR NATURALITY ═══════
    (associator_naturality := fun {X₁ X₂ X₃ Y₁ Y₂ Y₃} f₁ f₂ f₃ => by
      apply Hom.ext
      · change
          (assocAux Y₁.even Y₁.odd Y₂.even Y₂.odd Y₃.even Y₃.odd).toLinearMap ∘ₗ
          LinearMap.prodMap
              (TensorProduct.map
                (LinearMap.prodMap (TensorProduct.map f₁.evenMap f₂.evenMap)
                  (TensorProduct.map f₁.oddMap f₂.oddMap)) f₃.evenMap)
              (TensorProduct.map
                (LinearMap.prodMap (TensorProduct.map f₁.evenMap f₂.oddMap)
                  (TensorProduct.map f₁.oddMap f₂.evenMap)) f₃.oddMap) =
          LinearMap.prodMap
              (TensorProduct.map f₁.evenMap
                (LinearMap.prodMap (TensorProduct.map f₂.evenMap f₃.evenMap)
                  (TensorProduct.map f₂.oddMap f₃.oddMap)))
              (TensorProduct.map f₁.oddMap
                (LinearMap.prodMap (TensorProduct.map f₂.evenMap f₃.oddMap)
                  (TensorProduct.map f₂.oddMap f₃.evenMap))) ∘ₗ
          (assocAux X₁.even X₁.odd X₂.even X₂.odd X₃.even X₃.odd).toLinearMap
        ext x
        all_goals simp
      · change
          (assocAux Y₁.even Y₁.odd Y₂.even Y₂.odd Y₃.odd Y₃.even).toLinearMap ∘ₗ
          LinearMap.prodMap
              (TensorProduct.map
                (LinearMap.prodMap (TensorProduct.map f₁.evenMap f₂.evenMap)
                  (TensorProduct.map f₁.oddMap f₂.oddMap)) f₃.oddMap)
              (TensorProduct.map
                (LinearMap.prodMap (TensorProduct.map f₁.evenMap f₂.oddMap)
                  (TensorProduct.map f₁.oddMap f₂.evenMap)) f₃.evenMap) =
          LinearMap.prodMap
              (TensorProduct.map f₁.evenMap
                (LinearMap.prodMap (TensorProduct.map f₂.evenMap f₃.oddMap)
                  (TensorProduct.map f₂.oddMap f₃.evenMap)))
              (TensorProduct.map f₁.oddMap
                (LinearMap.prodMap (TensorProduct.map f₂.evenMap f₃.evenMap)
                  (TensorProduct.map f₂.oddMap f₃.oddMap))) ∘ₗ
          (assocAux X₁.even X₁.odd X₂.even X₂.odd X₃.odd X₃.even).toLinearMap
        ext x
        all_goals simp)
    -- ═══════ LEFT UNITOR NATURALITY ═══════
    (leftUnitor_naturality := fun {X Y} (f : X ⟶ Y) => by
      apply Hom.ext
      · -- even component
        change ((TensorProduct.lid ℂ Y.even).toLinearMap.comp (LinearMap.fst ℂ _
          _)).comp
            (LinearMap.prodMap (TensorProduct.map LinearMap.id f.evenMap)
              (TensorProduct.map LinearMap.id f.oddMap)) =
          f.evenMap.comp
            ((TensorProduct.lid ℂ X.even).toLinearMap.comp (LinearMap.fst ℂ _
              _))
        apply LinearMap.ext; intro ⟨x, y⟩
        simp only [LinearMap.comp_apply, LinearMap.fst_apply,
          LinearMap.prodMap_apply,
          LinearEquiv.coe_toLinearMap]
        induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul r m => simp [TensorProduct.lid_tmul, TensorProduct.map_tmul,
          map_smul]
        | add x₁ x₂ hx₁ hx₂ => simp only [map_add, hx₁, hx₂]
      · -- odd component
        change ((TensorProduct.lid ℂ Y.odd).toLinearMap.comp (LinearMap.fst ℂ _
          _)).comp
            (LinearMap.prodMap (TensorProduct.map LinearMap.id f.oddMap)
              (TensorProduct.map LinearMap.id f.evenMap)) =
          f.oddMap.comp
            ((TensorProduct.lid ℂ X.odd).toLinearMap.comp (LinearMap.fst ℂ _ _))
        apply LinearMap.ext; intro ⟨x, y⟩
        simp only [LinearMap.comp_apply, LinearMap.fst_apply,
          LinearMap.prodMap_apply,
          LinearEquiv.coe_toLinearMap]
        induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul r m => simp [TensorProduct.lid_tmul, TensorProduct.map_tmul,
          map_smul]
        | add x₁ x₂ hx₁ hx₂ => simp only [map_add, hx₁, hx₂])
    -- ═══════ RIGHT UNITOR NATURALITY ═══════
    (rightUnitor_naturality := fun {X Y} (f : X ⟶ Y) => by
      apply Hom.ext
      · -- even component: (rid ∘ fst) ∘ prodMap (map f.e id) (map f.o id) = f.e
        --   ∘ (rid ∘ fst)
        change ((TensorProduct.rid ℂ Y.even).toLinearMap.comp (LinearMap.fst ℂ _
          _)).comp
            (LinearMap.prodMap (TensorProduct.map f.evenMap LinearMap.id)
              (TensorProduct.map f.oddMap LinearMap.id)) =
          f.evenMap.comp
            ((TensorProduct.rid ℂ X.even).toLinearMap.comp (LinearMap.fst ℂ _
              _))
        apply LinearMap.ext; intro ⟨x, y⟩
        simp only [LinearMap.comp_apply, LinearMap.fst_apply,
          LinearMap.prodMap_apply,
          LinearEquiv.coe_toLinearMap]
        induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul m r => simp [TensorProduct.rid_tmul, TensorProduct.map_tmul,
          map_smul]
        | add x₁ x₂ hx₁ hx₂ => simp only [map_add, hx₁, hx₂]
      · -- odd component: (rid ∘ snd) ∘ prodMap (map f.e id) (map f.o id) = f.o
        --   ∘ (rid ∘ snd)
        change ((TensorProduct.rid ℂ Y.odd).toLinearMap.comp (LinearMap.snd ℂ _
          _)).comp
            (LinearMap.prodMap (TensorProduct.map f.evenMap LinearMap.id)
              (TensorProduct.map f.oddMap LinearMap.id)) =
          f.oddMap.comp
            ((TensorProduct.rid ℂ X.odd).toLinearMap.comp (LinearMap.snd ℂ _ _))
        apply LinearMap.ext; intro ⟨x, y⟩
        simp only [LinearMap.comp_apply, LinearMap.snd_apply,
          LinearMap.prodMap_apply,
          LinearEquiv.coe_toLinearMap]
        induction y using TensorProduct.induction_on with
        | zero => simp
        | tmul m r => simp [TensorProduct.rid_tmul, TensorProduct.map_tmul,
          map_smul]
        | add y₁ y₂ hy₁ hy₂ => simp only [map_add, hy₁, hy₂])
    -- ═══════ PENTAGON AND TRIANGLE ═══════
    (pentagon := fun W X Y Z => by
      apply Hom.ext
      · exact assocAux_pentagon W.even W.odd X.even X.odd
          Y.even Y.odd Z.even Z.odd
      · exact assocAux_pentagon W.even W.odd X.even X.odd
          Y.even Y.odd Z.odd Z.even)
    (triangle := fun X Y => by
      apply Hom.ext
      · exact assocAux_triangle X.even X.odd Y.even Y.odd
      · exact assocAux_triangle X.even X.odd Y.odd Y.even)

/-! ### Braided and symmetric structure -/

/-- SuperVect is a braided monoidal category with the Koszul
braiding: swapping odd ⊗ odd elements picks up a factor of −1. -/
instance instBraidedCategory : BraidedCategory SuperVect where
  braiding := koszulBraidingIso
  braiding_naturality_right := fun X {Y Z} f => by
    apply Hom.ext
    · -- even component
      change (koszulBraidingEven X Z).comp
          (LinearMap.prodMap (TensorProduct.map LinearMap.id f.evenMap)
            (TensorProduct.map LinearMap.id f.oddMap)) =
        (LinearMap.prodMap (TensorProduct.map f.evenMap LinearMap.id)
            (TensorProduct.map f.oddMap LinearMap.id)).comp
          (koszulBraidingEven X Y)
      apply LinearMap.ext; intro ⟨x, y⟩
      simp only [LinearMap.comp_apply, LinearMap.prodMap_apply,
        koszulBraidingEven, koszulEvenAux,
        LinearMap.neg_apply, LinearEquiv.coe_toLinearMap, Prod.mk.injEq]
      refine ⟨?_, ?_⟩
      · induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul a b => simp [TensorProduct.comm_tmul, TensorProduct.map_tmul]
        | add x₁ x₂ hx₁ hx₂ => simp only [map_add, hx₁, hx₂]
      · induction y using TensorProduct.induction_on with
        | zero => simp
        | tmul a b =>
          simp [TensorProduct.comm_tmul, TensorProduct.map_tmul, map_neg]
        | add y₁ y₂ hy₁ hy₂ =>
          simp only [map_add, neg_add]; exact congr_arg₂ (· + ·) hy₁ hy₂
    · -- odd component
      change (koszulBraidingOdd X Z).comp
          (LinearMap.prodMap (TensorProduct.map LinearMap.id f.oddMap)
            (TensorProduct.map LinearMap.id f.evenMap)) =
        (LinearMap.prodMap (TensorProduct.map f.evenMap LinearMap.id)
            (TensorProduct.map f.oddMap LinearMap.id)).comp
          (koszulBraidingOdd X Y)
      apply LinearMap.ext; intro ⟨x, y⟩
      simp only [LinearMap.comp_apply, LinearMap.prodMap_apply,
        koszulBraidingOdd_pair, Prod.mk.injEq]
      refine ⟨?_, ?_⟩
      · induction y using TensorProduct.induction_on with
        | zero => simp
        | tmul a b => simp [TensorProduct.comm_tmul, TensorProduct.map_tmul]
        | add y₁ y₂ hy₁ hy₂ => simp only [map_add, hy₁, hy₂]
      · induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul a b => simp [TensorProduct.comm_tmul, TensorProduct.map_tmul]
        | add x₁ x₂ hx₁ hx₂ => simp only [map_add, hx₁, hx₂]
  braiding_naturality_left := fun {X Y} f Z => by
    apply Hom.ext
    · -- even component
      change (koszulBraidingEven Y Z).comp
          (LinearMap.prodMap (TensorProduct.map f.evenMap LinearMap.id)
            (TensorProduct.map f.oddMap LinearMap.id)) =
        (LinearMap.prodMap (TensorProduct.map LinearMap.id f.evenMap)
            (TensorProduct.map LinearMap.id f.oddMap)).comp
          (koszulBraidingEven X Z)
      apply LinearMap.ext; intro ⟨x, y⟩
      simp only [LinearMap.comp_apply, LinearMap.prodMap_apply,
        koszulBraidingEven, koszulEvenAux,
        LinearMap.neg_apply, LinearEquiv.coe_toLinearMap, Prod.mk.injEq]
      refine ⟨?_, ?_⟩
      · induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul a b => simp [TensorProduct.comm_tmul, TensorProduct.map_tmul]
        | add x₁ x₂ hx₁ hx₂ => simp only [map_add, hx₁, hx₂]
      · induction y using TensorProduct.induction_on with
        | zero => simp
        | tmul a b =>
          simp [TensorProduct.comm_tmul, TensorProduct.map_tmul, map_neg]
        | add y₁ y₂ hy₁ hy₂ =>
          simp only [map_add, neg_add]; exact congr_arg₂ (· + ·) hy₁ hy₂
    · -- odd component
      change (koszulBraidingOdd Y Z).comp
          (LinearMap.prodMap (TensorProduct.map f.evenMap LinearMap.id)
            (TensorProduct.map f.oddMap LinearMap.id)) =
        (LinearMap.prodMap (TensorProduct.map LinearMap.id f.oddMap)
            (TensorProduct.map LinearMap.id f.evenMap)).comp
          (koszulBraidingOdd X Z)
      apply LinearMap.ext; intro ⟨x, y⟩
      simp only [LinearMap.comp_apply, LinearMap.prodMap_apply,
        koszulBraidingOdd_pair, Prod.mk.injEq]
      refine ⟨?_, ?_⟩
      · induction y using TensorProduct.induction_on with
        | zero => simp
        | tmul a b => simp [TensorProduct.comm_tmul, TensorProduct.map_tmul]
        | add y₁ y₂ hy₁ hy₂ => simp only [map_add, hy₁, hy₂]
      · induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul a b => simp [TensorProduct.comm_tmul, TensorProduct.map_tmul]
        | add x₁ x₂ hx₁ hx₂ => simp only [map_add, hx₁, hx₂]
  hexagon_forward := fun X Y Z => by
    apply Hom.ext
    · exact koszulAux_hexagon_fwd_even X.even X.odd Y.even Y.odd
        Z.even Z.odd
    · exact koszulAux_hexagon_fwd_odd X.even X.odd Y.even Y.odd
        Z.even Z.odd
  hexagon_reverse := fun X Y Z => by
    apply Hom.ext
    · exact koszulAux_hexagon_rev_even X.even X.odd Y.even Y.odd
        Z.even Z.odd
    · exact koszulAux_hexagon_rev_odd X.even X.odd Y.even Y.odd
        Z.even Z.odd

/-- SuperVect is a symmetric monoidal category: applying the
Koszul braiding twice recovers the identity. -/
instance instSymmetricCategory : SymmetricCategory SuperVect where
  symmetry := fun X Y => koszulBraiding_self_inverse X Y

/-! ### Additive and linear structure -/

/-- The zero morphism: zero in both components. -/
instance {V W : SuperVect} : Zero (V ⟶ W) :=
  ⟨⟨0, 0⟩⟩

/-- Componentwise addition of morphisms. -/
instance {V W : SuperVect} : Add (V ⟶ W) :=
  ⟨fun f g => ⟨f.evenMap + g.evenMap, f.oddMap + g.oddMap⟩⟩

/-- Componentwise negation. -/
instance {V W : SuperVect} : Neg (V ⟶ W) :=
  ⟨fun f => ⟨-f.evenMap, -f.oddMap⟩⟩

/-- Componentwise subtraction. -/
instance {V W : SuperVect} : Sub (V ⟶ W) :=
  ⟨fun f g => ⟨f.evenMap - g.evenMap, f.oddMap - g.oddMap⟩⟩

/-- Componentwise scaling by a complex number. -/
instance {V W : SuperVect} : SMul ℂ (V ⟶ W) :=
  ⟨fun c f => ⟨c • f.evenMap, c • f.oddMap⟩⟩

/-- Componentwise natural scaling, given definitionally so that the
`AddCommGroup` structure below has no transported `nsmul` field. -/
instance {V W : SuperVect} : SMul ℕ (V ⟶ W) :=
  ⟨fun n f => ⟨n • f.evenMap, n • f.oddMap⟩⟩

/-- Componentwise integer scaling, likewise definitional. -/
instance {V W : SuperVect} : SMul ℤ (V ⟶ W) :=
  ⟨fun n f => ⟨n • f.evenMap, n • f.oddMap⟩⟩

/-- The components of a morphism determine it; the additive and
module structures are pulled back componentwise. -/
private def homComponents {V W : SuperVect} (f : V ⟶ W) :
    (V.even →ₗ[ℂ] W.even) × (V.odd →ₗ[ℂ] W.odd) :=
  (f.evenMap, f.oddMap)

private theorem homComponents_injective {V W : SuperVect} :
    Function.Injective (homComponents (V := V) (W := W)) :=
  fun _ _ h => Hom.ext (congrArg Prod.fst h) (congrArg Prod.snd h)

/-- Morphisms form an abelian group, pulled back along the injection
into the pair of component maps. -/
instance {V W : SuperVect} : AddCommGroup (V ⟶ W) :=
  homComponents_injective.addCommGroup homComponents
    rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)

/-- Morphisms form a ℂ-module, pulled back the same way: SuperVect
is ℂ-linear. -/
instance {V W : SuperVect} : Module ℂ (V ⟶ W) :=
  homComponents_injective.module ℂ
    { toFun := homComponents
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
    (fun _ _ => rfl)

/-- Addition of morphisms is componentwise on the even part. -/
@[simp]
theorem add_evenMap {V W : SuperVect} (f g : V ⟶ W) :
    (f + g).evenMap = f.evenMap + g.evenMap := rfl

/-- Addition of morphisms is componentwise on the odd part. -/
@[simp]
theorem add_oddMap {V W : SuperVect} (f g : V ⟶ W) :
    (f + g).oddMap = f.oddMap + g.oddMap := rfl

/-- The zero morphism's even component is zero. -/
@[simp]
theorem zero_evenMap {V W : SuperVect} :
    (0 : V ⟶ W).evenMap = 0 := rfl

/-- The zero morphism's odd component is zero. -/
@[simp]
theorem zero_oddMap {V W : SuperVect} :
    (0 : V ⟶ W).oddMap = 0 := rfl

/-- Scalar multiplication is componentwise on the even part. -/
@[simp]
theorem smul_evenMap {V W : SuperVect} (c : ℂ) (f : V ⟶ W) :
    (c • f).evenMap = c • f.evenMap := rfl

/-- Scalar multiplication is componentwise on the odd part. -/
@[simp]
theorem smul_oddMap {V W : SuperVect} (c : ℂ) (f : V ⟶ W) :
    (c • f).oddMap = c • f.oddMap := rfl

/-- SuperVect is preadditive: composition is bilinear
componentwise. -/
instance instPreadditive : Preadditive SuperVect where
  add_comp _ _ _ f f' g := by
    apply Hom.ext
    · show g.evenMap ∘ₗ (f.evenMap + f'.evenMap) = _
      exact LinearMap.comp_add _ _ _
    · show g.oddMap ∘ₗ (f.oddMap + f'.oddMap) = _
      exact LinearMap.comp_add _ _ _
  comp_add _ _ _ f g g' := by
    apply Hom.ext
    · show (g.evenMap + g'.evenMap) ∘ₗ f.evenMap = _
      exact LinearMap.add_comp _ _ _
    · show (g.oddMap + g'.oddMap) ∘ₗ f.oddMap = _
      exact LinearMap.add_comp _ _ _

/-- SuperVect is ℂ-linear: composition is ℂ-bilinear
componentwise. -/
instance instLinear : CategoryTheory.Linear ℂ SuperVect where
  smul_comp _ _ _ c f g := by
    apply Hom.ext
    · show g.evenMap ∘ₗ (c • f.evenMap) = _
      exact LinearMap.comp_smul _ _ _
    · show g.oddMap ∘ₗ (c • f.oddMap) = _
      exact LinearMap.comp_smul _ _ _
  comp_smul _ _ _ f c g := by
    apply Hom.ext
    · show (c • g.evenMap) ∘ₗ f.evenMap = _
      exact LinearMap.smul_comp _ _ _
    · show (c • g.oddMap) ∘ₗ f.oddMap = _
      exact LinearMap.smul_comp _ _ _

/-! ### Unit-prefixed associator and braiding values -/

/-- The unit-prefixed associator on the even-even block. -/
theorem assoc_unit_ee {V : SuperVect} (r : ℂ) (x y : V.even) :
    (associator tensorUnit V V).hom.evenMap
      (((r ⊗ₜ[ℂ] x, (0 : tensorUnit.odd ⊗[ℂ] V.odd)) ⊗ₜ[ℂ] y,
        (0 : ((tensorUnit.even ⊗[ℂ] V.odd) ×
          (tensorUnit.odd ⊗[ℂ] V.even)) ⊗[ℂ] V.odd))) =
      ((r ⊗ₜ[ℂ] ((x ⊗ₜ[ℂ] y,
          (0 : V.odd ⊗[ℂ] V.odd)) :
        (tensorObj V V).even)),
        (0 : tensorUnit.odd ⊗[ℂ] (tensorObj V V).odd)) := by
  show assocEvenEquiv tensorUnit V V _ = _
  exact assocAux_ee r x y

/-- The unit-prefixed associator on the odd-odd block. -/
theorem assoc_unit_oo {V : SuperVect} (r : ℂ) (u v : V.odd) :
    (associator tensorUnit V V).hom.evenMap
      (((0 : ((tensorUnit.even ⊗[ℂ] V.even) ×
          (tensorUnit.odd ⊗[ℂ] V.odd)) ⊗[ℂ] V.even),
        (r ⊗ₜ[ℂ] u, (0 : tensorUnit.odd ⊗[ℂ] V.even))
          ⊗ₜ[ℂ] v)) =
      ((r ⊗ₜ[ℂ] (((0 : V.even ⊗[ℂ] V.even),
          u ⊗ₜ[ℂ] v) :
        (tensorObj V V).even)),
        (0 : tensorUnit.odd ⊗[ℂ] (tensorObj V V).odd)) := by
  show assocEvenEquiv tensorUnit V V _ = _
  exact assocAux_eo r u v

/-- The unit-prefixed associator on the even-odd block. -/
theorem assoc_unit_eo {V : SuperVect} (r : ℂ)
    (x : V.even) (v : V.odd) :
    (associator tensorUnit V V).hom.oddMap
      (((r ⊗ₜ[ℂ] x, (0 : tensorUnit.odd ⊗[ℂ] V.odd))
          ⊗ₜ[ℂ] v,
        (0 : ((tensorUnit.even ⊗[ℂ] V.odd) ×
          (tensorUnit.odd ⊗[ℂ] V.even)) ⊗[ℂ] V.even))) =
      ((r ⊗ₜ[ℂ] ((x ⊗ₜ[ℂ] v,
          (0 : V.odd ⊗[ℂ] V.even)) :
        (tensorObj V V).odd)),
        (0 : tensorUnit.odd ⊗[ℂ] (tensorObj V V).even)) := by
  show assocOddEquiv tensorUnit V V _ = _
  exact assocAux_ee r x v

/-- The unit-prefixed associator on the odd-even block. -/
theorem assoc_unit_oe {V : SuperVect} (r : ℂ)
    (u : V.odd) (y : V.even) :
    (associator tensorUnit V V).hom.oddMap
      (((0 : ((tensorUnit.even ⊗[ℂ] V.even) ×
          (tensorUnit.odd ⊗[ℂ] V.odd)) ⊗[ℂ] V.odd),
        (r ⊗ₜ[ℂ] u, (0 : tensorUnit.odd ⊗[ℂ] V.even))
          ⊗ₜ[ℂ] y)) =
      ((r ⊗ₜ[ℂ] (((0 : V.even ⊗[ℂ] V.odd),
          u ⊗ₜ[ℂ] y) :
        (tensorObj V V).odd)),
        (0 : tensorUnit.odd ⊗[ℂ] (tensorObj V V).even)) := by
  show assocOddEquiv tensorUnit V V _ = _
  exact assocAux_eo r u y

/-- The braiding on the even-even block. -/
theorem koszul_ee {V W : SuperVect} (x : V.even) (w : W.even) :
    (koszulBraiding V W).evenMap
      ((x ⊗ₜ[ℂ] w, (0 : V.odd ⊗[ℂ] W.odd))) =
      ((w ⊗ₜ[ℂ] x, (0 : W.odd ⊗[ℂ] V.odd))) := by
  show koszulBraidingEven V W _ = _
  simp [koszulBraidingEven, koszulEvenAux]

/-- The braiding on the odd-odd block: the Koszul sign. -/
theorem koszul_oo {V W : SuperVect} (u : V.odd) (v : W.odd) :
    (koszulBraiding V W).evenMap
      (((0 : V.even ⊗[ℂ] W.even), u ⊗ₜ[ℂ] v)) =
      (((0 : W.even ⊗[ℂ] V.even), -(v ⊗ₜ[ℂ] u))) := by
  show koszulBraidingEven V W _ = _
  simp [koszulBraidingEven, koszulEvenAux]

/-- The braiding on the even-odd block. -/
theorem koszul_eo {V W : SuperVect} (x : V.even) (v : W.odd) :
    (koszulBraiding V W).oddMap
      ((x ⊗ₜ[ℂ] v, (0 : V.odd ⊗[ℂ] W.even))) =
      (((0 : W.even ⊗[ℂ] V.odd), v ⊗ₜ[ℂ] x)) := by
  show koszulBraidingOdd V W _ = _
  simp [koszulBraidingOdd, koszulOddAux]

/-- The braiding on the odd-even block. -/
theorem koszul_oe {V W : SuperVect} (u : V.odd) (w : W.even) :
    (koszulBraiding V W).oddMap
      (((0 : V.even ⊗[ℂ] W.odd), u ⊗ₜ[ℂ] w)) =
      ((w ⊗ₜ[ℂ] u, (0 : W.odd ⊗[ℂ] V.even))) := by
  show koszulBraidingOdd V W _ = _
  simp [koszulBraidingOdd, koszulOddAux]

/-- The unit-prefixed inverse associator on the even-even
block. -/
theorem assoc_unit_inv_ee {V : SuperVect} (r : ℂ)
    (x y : V.even) :
    (associator tensorUnit V V).inv.evenMap
      ((r ⊗ₜ[ℂ] ((x ⊗ₜ[ℂ] y,
          (0 : V.odd ⊗[ℂ] V.odd)) :
        (tensorObj V V).even)),
        (0 : tensorUnit.odd ⊗[ℂ] (tensorObj V V).odd)) =
      (((r ⊗ₜ[ℂ] x, (0 : tensorUnit.odd ⊗[ℂ] V.odd))
          ⊗ₜ[ℂ] y,
        (0 : ((tensorUnit.even ⊗[ℂ] V.odd) ×
          (tensorUnit.odd ⊗[ℂ] V.even)) ⊗[ℂ] V.odd))) := by
  show (assocEvenEquiv tensorUnit V V).symm _ = _
  exact (LinearEquiv.symm_apply_eq _).mpr (assocAux_ee r x y).symm

/-- The unit-prefixed inverse associator on the odd-odd block. -/
theorem assoc_unit_inv_oo {V : SuperVect} (r : ℂ)
    (u v : V.odd) :
    (associator tensorUnit V V).inv.evenMap
      ((r ⊗ₜ[ℂ] (((0 : V.even ⊗[ℂ] V.even),
          u ⊗ₜ[ℂ] v) :
        (tensorObj V V).even)),
        (0 : tensorUnit.odd ⊗[ℂ] (tensorObj V V).odd)) =
      (((0 : ((tensorUnit.even ⊗[ℂ] V.even) ×
          (tensorUnit.odd ⊗[ℂ] V.odd)) ⊗[ℂ] V.even),
        (r ⊗ₜ[ℂ] u, (0 : tensorUnit.odd ⊗[ℂ] V.even))
          ⊗ₜ[ℂ] v)) := by
  show (assocEvenEquiv tensorUnit V V).symm _ = _
  exact (LinearEquiv.symm_apply_eq _).mpr (assocAux_eo r u v).symm

/-- The unit-prefixed inverse associator on the even-odd block. -/
theorem assoc_unit_inv_eo {V : SuperVect} (r : ℂ)
    (x : V.even) (v : V.odd) :
    (associator tensorUnit V V).inv.oddMap
      ((r ⊗ₜ[ℂ] ((x ⊗ₜ[ℂ] v,
          (0 : V.odd ⊗[ℂ] V.even)) :
        (tensorObj V V).odd)),
        (0 : tensorUnit.odd ⊗[ℂ] (tensorObj V V).even)) =
      (((r ⊗ₜ[ℂ] x, (0 : tensorUnit.odd ⊗[ℂ] V.odd))
          ⊗ₜ[ℂ] v,
        (0 : ((tensorUnit.even ⊗[ℂ] V.odd) ×
          (tensorUnit.odd ⊗[ℂ] V.even)) ⊗[ℂ] V.even))) := by
  show (assocOddEquiv tensorUnit V V).symm _ = _
  exact (LinearEquiv.symm_apply_eq _).mpr (assocAux_ee r x v).symm

/-- The unit-prefixed inverse associator on the odd-even block. -/
theorem assoc_unit_inv_oe {V : SuperVect} (r : ℂ)
    (u : V.odd) (y : V.even) :
    (associator tensorUnit V V).inv.oddMap
      ((r ⊗ₜ[ℂ] (((0 : V.even ⊗[ℂ] V.odd),
          u ⊗ₜ[ℂ] y) :
        (tensorObj V V).odd)),
        (0 : tensorUnit.odd ⊗[ℂ] (tensorObj V V).even)) =
      (((0 : ((tensorUnit.even ⊗[ℂ] V.even) ×
          (tensorUnit.odd ⊗[ℂ] V.odd)) ⊗[ℂ] V.odd),
        (r ⊗ₜ[ℂ] u, (0 : tensorUnit.odd ⊗[ℂ] V.even))
          ⊗ₜ[ℂ] y)) := by
  show (assocOddEquiv tensorUnit V V).symm _ = _
  exact (LinearEquiv.symm_apply_eq _).mpr (assocAux_eo r u y).symm

end SuperVect

end RS
