import EnvelopingIsomorphism.Deformation.MixedPairedOutgoingRelabelling

/-! The actual outgoing face-integral covariance survives the native profile
cast from a split graph into the marked one-vector carrier. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.MixedPairedProfileOutgoing
open Kontsevich KontsevichGraph.General MixedGraphProfileCarrier MixedPairedEdgeRelabelling
open scoped Classical BigOperators
theorem normalized_ofProfile_permuteOutgoing {N : ℕ} {i a b : Fin (N+1)}
    {S : Finset (Fin (N+1))} (ha : a ∈ S) (hb : b ∈ S) (hba : b ≠ a)
    (hi : i ∈ S → a = i) {q : Fin (N+1) → ℕ} (v : Fin (N+1))
    (hq : q = Gauge.PlacedMixedGraphTaylorCoefficients.arities 1 v)
    (G : Graph q 2) (τ : (w : Fin (N+1)) → Equiv.Perm (Fin (q w))) :
    normalized ha hb hba hi (ofProfile v hq (G.permuteOutgoing τ)) =
      (∏ w, permutationSign (R := ℝ) (τ w)) * normalized ha hb hba hi (ofProfile v hq G) := by
  subst q
  exact MixedPairedOutgoingRelabelling.normalized_permuted ⟨v,G⟩ τ ha hb hba hi

end EnvelopingIsomorphism.Deformation.MixedPairedProfileOutgoing
