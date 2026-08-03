import RS.Classical.Deligne.ZigzagTransfer

/-!
# Transport of the zigzag laws along isomorphisms

An isomorphism is a section–retraction pair whose composite
idempotent is the identity, so the adjointness condition of the
transfer is vacuous and the zigzag laws pass across without any
further hypothesis.
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

section TransferIso

variable {P P' Q Q' : Mod D A}
variable (d₀ : ModDualityDatum A P P')
variable (i : Q ≅ P) (i' : Q' ≅ P')

/-- **Transport of a duality datum along isomorphisms** of the
two modules. -/
noncomputable def ModDualityDatum.transferIso :
    ModDualityDatum A Q Q' :=
  d₀.transfer A i.hom i'.hom i.inv i'.inv

omit [Preadditive D] [MonoidalPreadditive D]
  [HasFiniteBiproducts D]
  [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair
    (tensorRight Z)] in
/-- The adjointness condition of the transfer is vacuous for
isomorphisms: both composite idempotents are identities. -/
theorem transferIso_adj :
    modTensorMap A (i'.inv ≫ i'.hom) (𝟙 P) ≫ d₀.pair =
      modTensorMap A (𝟙 P') (i.inv ≫ i.hom) ≫ d₀.pair := by
  rw [i.inv_hom_id, i'.inv_hom_id]

/-- **The zigzag laws transport along isomorphisms.** -/
theorem modZigzagDatum_transferIso (hz₀ : ModZigzagDatum A d₀) :
    ModZigzagDatum A (d₀.transferIso A i i') :=
  modZigzagDatum_transfer A d₀ i.hom i'.hom i.inv i'.inv hz₀
    i.hom_inv_id i'.hom_inv_id (transferIso_adj A d₀ i i')

end TransferIso

end RS
