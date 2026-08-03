import RS.Novel.Coordinates.CanonColour
import RS.Classical.Super.ColourFormMatch

/-!
# The Regts–Sevenster functional

The coordinates of the star vectors in the colouring model, and
the normalised mixed functional `h^RS` of the Main Theorem: the
`J`-twisted star coordinate at the canonical colouring of the
multiset data, `J` being the accompanying paper's parity-transfer
involution (§5.4).
-/

namespace RS

variable {R : ℕ} (f : EdgeRankParameter R)
variable (P : DelignePackage (SkeinObj f))
variable {k ℓ : ℕ}
variable (e' : P.ω.obj (SkeinObj.mk 1) ⟶ stdSuperPair k ℓ)

/-- The star coordinate: the vertex star vector transported to
the colouring model, read at a colouring; zero on odd-parity
colourings. -/
noncomputable def starCoord (d : ℕ)
    (c : MixedColouring k ℓ d) : ℂ :=
  if hc : c.IsEven then
    (colourPowerEquiv k ℓ d).evenEquiv
      (((stdFromOmega f P e' d) :
        SuperVect.Hom _ _).evenMap (starVec f P d)) ⟨c, hc⟩
  else 0

/-- Star coordinates vanish on odd-parity colourings. -/
theorem starCoord_odd (d : ℕ) (c : MixedColouring k ℓ d)
    (hc : ¬ c.IsEven) : starCoord f P e' d c = 0 :=
  dif_neg hc

/-- **The Regts–Sevenster functional**: the star coordinate at
the canonical colouring.  (The formal conventions absorb the
paper's parity-transfer involution `J`: the canonical ordering
already carries it.) -/
noncomputable def hRS : MixedFunctional k ℓ := fun μm F =>
  starCoord f P e' (μm.card + F.card) (canonColouring μm F)

/-- The alternating evaluation of the functional on a
duplicate-free list: sorting sign, normalisation sign, star
coordinate at the canonical colouring. -/
theorem evalOdd_hRS_nodup (μm : Multiset (Fin k))
    (w : List (Fin (2 * ℓ))) (hw : w.Nodup) :
    (hRS f P e').evalOdd μm w =
      (sortSign w : ℂ) *
        starCoord f P e' (μm.card + w.toFinset.card)
          (canonColouring μm w.toFinset) := by
  unfold MixedFunctional.evalOdd hRS
  rw [if_pos hw]

end RS
