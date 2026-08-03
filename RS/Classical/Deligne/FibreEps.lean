import RS.Classical.Deligne.GammaPairNat
import RS.Classical.Deligne.FreeModShuffle

/-!
# The unit comparison of the fibre functor

The free module of the tensor unit is the regular module, whose
realization is the Γ-algebra viewed over itself, that is, the unit
of the tensor product of super modules.  The unit comparison of the
fibre functor is therefore an isomorphism outright, and on the two
components it is composition with the inverse right unitor of the
algebra.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits

universe v u

section

variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
variable [SymmetricCategory D] [Preadditive D] [MonoidalPreadditive D]
variable [Linear ℂ D] [MonoidalLinear ℂ D]
variable (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R]

open SuperCommAlgebra.Mod

/-- **The unit comparison of the fibre functor.** -/
noncomputable def fibreEpsIso :
    (gammaAlgebra D L R).unitMod ≅
      gammaModule D L R (freeMod R (𝟙_ D)).X :=
  ((gammaModuleFunctor L R).mapIso (freeModUnitIso R)).symm

/-- The unit comparison, as a morphism. -/
noncomputable abbrev fibreEps :
    (gammaAlgebra D L R).unitMod ⟶
      gammaModule D L R (freeMod R (𝟙_ D)).X :=
  (fibreEpsIso L R).hom

/-- The unit comparison on the even component: composition with the
inverse right unitor of the algebra. -/
@[simp] theorem fibreEps_evenMap (x : 𝟙_ D ⟶ R) :
    (fibreEps L R).evenMap x = x ≫ (ρ_ R).inv := rfl

/-- The unit comparison on the odd component: composition with the
inverse right unitor of the algebra. -/
@[simp] theorem fibreEps_oddMap (u : L.obj ⟶ R) :
    (fibreEps L R).oddMap u = u ≫ (ρ_ R).inv := rfl

instance : IsIso (fibreEps L R) := (fibreEpsIso L R).isIso_hom

end

end RS
