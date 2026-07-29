import RS.Novel.Coordinates.BetaData
import RS.Novel.Coordinates.EdgeSign
import RS.Novel.Coordinates.OddSignProd
import RS.Novel.Coordinates.OutSignEdges
import RS.Novel.Coordinates.BlockAlign

/-!
# The cap pairing at the flipped colouring

Composing the diagonal cap evaluation, the flip's edge signs, the
per-edge collapse, and the vertex odd-sign product: the cap
pairing at the flipped data colouring is the crossing and
representative parities times the Definition 5 odd signs.
-/

namespace RS

open Classical Finset

variable {k ℓ : ℕ}

open Classical in
/-- **The cap pairing at the flipped data colouring**. -/
theorem betaDiag_colouringOfFlip (W : ClosedFragment)
    (F : EdgeSubset W) {κ : F.TransitionSystem}
    (o : κ.Orientation) (ψ : F.EvenColouring k)
    (φ : F.OddColouring ℓ) :
    betaDiag (edgeCount W) (colouringOfFlip W F o ψ φ) =
      (-1 : ℂ) ^ (Finset.univ.filter
          (fun p : Fin (edgeCount W) × Fin (edgeCount W) =>
            p.1 < p.2 ∧ p.1 ∈ edgeIndexSet W F ∧
            p.2 ∈ edgeIndexSet W F)).card *
        (-1 : ℂ) ^ inRepCount W F o *
        ∏ v : W.Vertex, ((F.oddSignAt o φ v : ℤ) : ℂ) := by
  rw [show colouringOfFlip W F o ψ φ =
    colouringOf W F ψ
      (EdgeSubset.OddColouring.flip F (outRepSet W F o)
        (outRepSet_pairing_mem W F o) φ) from rfl]
  rw [betaDiag_colouringOf W F ψ _]
  rw [edge_sign_sector W F o φ]
  rw [show (∏ i : Fin (edgeCount W),
      (if h : (starFlagEnum W).symm
          (Fin.castAdd (edgeCount W) i) ∈ F.flags then
        ((oddPartnerSign ℓ (φ.val
          ⟨(starFlagEnum W).symm
            (Fin.castAdd (edgeCount W) i), h⟩) : ℤ) : ℂ)
      else 1)) =
    ((∏ i : Fin (edgeCount W),
      (if h : (starFlagEnum W).symm
          (Fin.castAdd (edgeCount W) i) ∈ F.flags then
        oddPartnerSign ℓ (φ.val
          ⟨(starFlagEnum W).symm
            (Fin.castAdd (edgeCount W) i), h⟩)
      else 1) : ℤ) : ℂ) from by
    rw [Int.cast_prod]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [apply_dite (fun z : ℤ => (z : ℂ))]
    norm_num]
  rw [← prod_out_sign_eq_prod_edges W F o φ]
  rw [← prod_oddSignAt o φ]
  rw [Int.cast_prod]
  ring

end RS
