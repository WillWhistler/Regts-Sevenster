import RS.Classical.SchurTheory.KillSimples

/-!
# Kill criteria for the block development

Vanishing of the `ofModule` action is elementwise annihilation;
intertwiners commute with the whole algebra action, so
annihilation transports along equivalences of representations.
-/

namespace RS

open Finset LinearMap

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

omit [Fintype G] [DecidableEq G] in
/-- An intertwiner commutes with the algebra action. -/
theorem intertwiner_comp_asAlgebraHom
    {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (f : V →ₗ[ℂ] W) (hf : ∀ g : G, f ∘ₗ (ρ g : V →ₗ[ℂ] V) =
      (σ g : W →ₗ[ℂ] W) ∘ₗ f) (y : MonoidAlgebra ℂ G) :
    f ∘ₗ ρ.asAlgebraHom y = σ.asAlgebraHom y ∘ₗ f := by
  induction y using MonoidAlgebra.induction_on with
  | hM g =>
    rw [show MonoidAlgebra.of ℂ G g =
      MonoidAlgebra.single g (1 : ℂ) from rfl]
    rw [show (ρ.asAlgebraHom (MonoidAlgebra.single g 1) :
        V →ₗ[ℂ] V) = (ρ g : V →ₗ[ℂ] V) from by
      rw [Representation.asAlgebraHom_single, one_smul]]
    rw [show (σ.asAlgebraHom (MonoidAlgebra.single g 1) :
        W →ₗ[ℂ] W) = (σ g : W →ₗ[ℂ] W) from by
      rw [Representation.asAlgebraHom_single, one_smul]]
    exact hf g
  | hadd a b ha hb =>
    rw [map_add, map_add, LinearMap.comp_add, LinearMap.add_comp,
      ha, hb]
  | hsmul r a ha =>
    rw [map_smul, map_smul, LinearMap.comp_smul,
      LinearMap.smul_comp, ha]

variable (T : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G))

end RS
