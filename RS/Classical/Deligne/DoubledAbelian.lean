import RS.Classical.Deligne.Doubling

/-!
# Abelianness of the doubling

`RS/Classical/Deligne/Doubling.lean` equips the ℤ/2-graded
doubling `Doubled A` with componentwise binary biproducts, kernels
and cokernels.  This module upgrades that bookkeeping to
abelianness: if `A` is abelian, so is `Doubled A`.

The route is Mathlib's coimage–image criterion
`CategoryTheory.Abelian.ofCoimageImageComparisonIsIso`.  The two
component functors `evenFunctor`, `oddFunctor : Doubled A ⥤ A`
preserve kernels and cokernels, because the kernel and the cokernel
of a morphism of super-objects are the componentwise ones; hence
they preserve abelian images, abelian coimages, and the comparison
morphism between them.  Downstairs that comparison is an
isomorphism, so both components of the comparison upstairs are
isomorphisms, and `Doubled.isIso_of_components` concludes.
-/

namespace RS

open CategoryTheory CategoryTheory.Limits

universe v u

noncomputable section

namespace Doubled

section Components

variable {A : Type u} [Category.{v} A]

/-- The even-component functor `X ↦ X.even`. -/
def evenFunctor : Doubled A ⥤ A where
  obj X := X.even
  map f := evenHom f
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The odd-component functor `X ↦ X.odd`. -/
def oddFunctor : Doubled A ⥤ A where
  obj X := X.odd
  map f := oddHom f
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp]
theorem evenFunctor_obj (X : Doubled A) :
    (evenFunctor : Doubled A ⥤ A).obj X = X.even :=
  rfl

@[simp]
theorem oddFunctor_obj (X : Doubled A) :
    (oddFunctor : Doubled A ⥤ A).obj X = X.odd :=
  rfl

@[simp]
theorem evenFunctor_map {X Y : Doubled A} (f : X ⟶ Y) :
    (evenFunctor : Doubled A ⥤ A).map f = evenHom f :=
  rfl

@[simp]
theorem oddFunctor_map {X Y : Doubled A} (f : X ⟶ Y) :
    (oddFunctor : Doubled A ⥤ A).map f = oddHom f :=
  rfl

/-- The even-component functor preserves zero morphisms. -/
instance evenFunctorPreservesZeroMorphisms [Preadditive A] :
    (evenFunctor : Doubled A ⥤ A).PreservesZeroMorphisms where
  map_zero _ _ := rfl

/-- The odd-component functor preserves zero morphisms. -/
instance oddFunctorPreservesZeroMorphisms [Preadditive A] :
    (oddFunctor : Doubled A ⥤ A).PreservesZeroMorphisms where
  map_zero _ _ := rfl

end Components

section Exactness

variable {A : Type u} [Category.{v} A] [Preadditive A]

/-- The even-component functor preserves kernels: the kernel of a
morphism of super-objects is the componentwise one. -/
instance evenFunctorPreservesKernel [HasKernels A] {X Y : Doubled A}
    (f : X ⟶ Y) :
    PreservesLimit (parallelPair f 0) (evenFunctor : Doubled A ⥤ A) :=
  preservesLimit_of_preserves_limit_cone (kernelForkIsLimit f)
    ((KernelFork.isLimitMapConeEquiv (kernelFork f) evenFunctor).symm
      (kernelIsKernel (evenHom f)))

/-- The odd-component functor preserves kernels. -/
instance oddFunctorPreservesKernel [HasKernels A] {X Y : Doubled A}
    (f : X ⟶ Y) :
    PreservesLimit (parallelPair f 0) (oddFunctor : Doubled A ⥤ A) :=
  preservesLimit_of_preserves_limit_cone (kernelForkIsLimit f)
    ((KernelFork.isLimitMapConeEquiv (kernelFork f) oddFunctor).symm
      (kernelIsKernel (oddHom f)))

/-- The even-component functor preserves cokernels: the cokernel of
a morphism of super-objects is the componentwise one. -/
instance evenFunctorPreservesCokernel [HasCokernels A]
    {X Y : Doubled A} (f : X ⟶ Y) :
    PreservesColimit (parallelPair f 0) (evenFunctor : Doubled A ⥤ A) :=
  preservesColimit_of_preserves_colimit_cocone (cokernelCoforkIsColimit f)
    ((CokernelCofork.isColimitMapCoconeEquiv (cokernelCofork f)
      evenFunctor).symm (cokernelIsCokernel (evenHom f)))

/-- The odd-component functor preserves cokernels. -/
instance oddFunctorPreservesCokernel [HasCokernels A]
    {X Y : Doubled A} (f : X ⟶ Y) :
    PreservesColimit (parallelPair f 0) (oddFunctor : Doubled A ⥤ A) :=
  preservesColimit_of_preserves_colimit_cocone (cokernelCoforkIsColimit f)
    ((CokernelCofork.isColimitMapCoconeEquiv (cokernelCofork f)
      oddFunctor).symm (cokernelIsCokernel (oddHom f)))

end Exactness

section Abelian

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The even component of the coimage–image comparison is an
isomorphism: it is, up to the comparison isomorphisms of the
even-component functor, the coimage–image comparison of `evenHom f`
in the abelian category `A`. -/
theorem isIso_evenHom_coimageImageComparison {X Y : Doubled A}
    (f : X ⟶ Y) :
    IsIso (evenHom (Abelian.coimageImageComparison f)) := by
  have h : IsIso ((evenFunctor : Doubled A ⥤ A).map
      (Abelian.coimageImageComparison f)) := by
    rw [Arrow.isIso_iff_isIso_of_isIso
      (Abelian.PreservesCoimageImageComparison.iso
        (evenFunctor : Doubled A ⥤ A) f).hom]
    infer_instance
  exact h

/-- The odd component of the coimage–image comparison is an
isomorphism, for the same reason. -/
theorem isIso_oddHom_coimageImageComparison {X Y : Doubled A}
    (f : X ⟶ Y) :
    IsIso (oddHom (Abelian.coimageImageComparison f)) := by
  have h : IsIso ((oddFunctor : Doubled A ⥤ A).map
      (Abelian.coimageImageComparison f)) := by
    rw [Arrow.isIso_iff_isIso_of_isIso
      (Abelian.PreservesCoimageImageComparison.iso
        (oddFunctor : Doubled A ⥤ A) f).hom]
    infer_instance
  exact h

/-- The coimage–image comparison of a morphism of super-objects is
an isomorphism, since both of its components are. -/
theorem isIso_coimageImageComparison {X Y : Doubled A} (f : X ⟶ Y) :
    IsIso (Abelian.coimageImageComparison f) :=
  haveI := isIso_evenHom_coimageImageComparison f
  haveI := isIso_oddHom_coimageImageComparison f
  isIso_of_components _

/-- The doubling of an abelian category is abelian, with
componentwise kernels, cokernels and biproducts. -/
instance instAbelian : Abelian (Doubled A) :=
  haveI : ∀ {X Y : Doubled A} (f : X ⟶ Y),
      IsIso (Abelian.coimageImageComparison f) :=
    fun f => isIso_coimageImageComparison f
  Abelian.ofCoimageImageComparisonIsIso

/-- The doubling has finite biproducts. -/
theorem hasFiniteBiproducts : HasFiniteBiproducts (Doubled A) :=
  Abelian.hasFiniteBiproducts

end Abelian

end Doubled

end

end RS
