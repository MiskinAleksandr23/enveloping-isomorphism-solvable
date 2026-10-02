import EnvelopingIsomorphism.Deformation.GeneralGraphGraftExtraction
import EnvelopingIsomorphism.Deformation.GraphGeneralWeightedGraft

/-! Exact scalar fibre coefficients of extracted boundary grafts. The
finite reconstruction bijection is used, rather than assumed graph matching. -/

noncomputable section
namespace EnvelopingIsomorphism.Deformation.GraphGeneralWeightedGraft
open KontsevichGraph.General GraphCoefficientProfiles
open scoped BigOperators Classical

variable {k : Type*} [CommRing k] {a b m l : ℕ}
  {q : Fin a → ℕ} {p : Fin b → ℕ}

private theorem pushforward_injective {I A : Type*} [Fintype I]
    (f : I → A) (hf : Function.Injective f) (w : I → k) (i : I) :
    pushforward f w (f i) = w i := by
  simp only [pushforward, hf.eq_iff]
  simp

/-- For a fixed actual partition and external block, the scalar graft fibre
has the weight product of the uniquely extracted pair, with no multiplicity lost. -/
theorem graftProfile_eq_extractedProduct (r : Fin (m + 1))
    (w : Graph q (m + 1) → k) (v : Graph p (l + 1) → k)
    (H : Graph (graftArity q p) (m + l + 1))
    (hc : H.InnerClosed r) (hd : H.CoarseDistinct r) :
    graftProfile r w v H = w (H.extractedOuter r hd) * v (H.extractedInner r hc) := by
  let D : Graph.GraftData q p r l :=
    ⟨H.extractedOuter r hd, H.extractedInner r hc, H.extractedChoices r hd⟩
  have hD : Graph.graftDataGraph r D = H := H.graft_extracted r hc hd
  change pushforward (Graph.graftDataGraph r)
    (fun E : Graph.GraftData q p r l ↦ w E.1 * v E.2.1) H = _
  calc
    _ = pushforward (Graph.graftDataGraph r)
        (fun E : Graph.GraftData q p r l ↦ w E.1 * v E.2.1) (Graph.graftDataGraph r D) :=
      congrArg _ hD.symm
    _ = w D.1 * v D.2.1 := pushforward_injective _ (Graph.graftDataGraph_injective r) _ D
    _ = _ := rfl

/-- Graphs outside the actual admissible graft boundary class have empty
graft fibres. Their geometric face term is treated by the separate vanishing lemmas. -/
theorem graftProfile_eq_zero_of_not_admissible (r : Fin (m + 1))
    (w : Graph q (m + 1) → k) (v : Graph p (l + 1) → k)
    (H : Graph (graftArity q p) (m + l + 1))
    (hH : ¬ (H.InnerClosed r ∧ H.CoarseDistinct r)) : graftProfile r w v H = 0 := by
  change (∑ D : Graph.GraftData q p r l,
    if Graph.graftDataGraph r D = H then w D.1 * v D.2.1 else 0) = 0
  apply Finset.sum_eq_zero
  intro D hD
  apply if_neg
  intro he
  apply hH
  rw [← he]
  exact ⟨Graph.graft_innerClosed r D.1 D.2.1 D.2.2,
    Graph.graft_coarseDistinct r D.1 D.2.1 D.2.2⟩

/-- The actual boundary-graph sum is exactly the full graft-data sum,
including the recovered incoming-edge assignment as part of the finite bijection. -/
theorem sum_extracted_products_eq_graft_sum
    {V : Type*} [AddCommGroup V] [Module k V]
    (r : Fin (m + 1)) (w : Graph q (m + 1) → k) (v : Graph p (l + 1) → k)
    (F : Graph (graftArity q p) (m + l + 1) → V) :
    (∑ H : {H : Graph (graftArity q p) (m + l + 1) // H.InnerClosed r ∧ H.CoarseDistinct r},
      (w (H.val.extractedOuter r H.property.2) * v (H.val.extractedInner r H.property.1)) • F H.val) =
      ∑ D : Graph.GraftData q p r l, (w D.1 * v D.2.1) • F (Graph.graftDataGraph r D) := by
  apply Fintype.sum_equiv (Graph.graftExtractionEquiv q p r l).symm
  intro H
  change _ = (w (H.val.extractedOuter r H.property.2) * v (H.val.extractedInner r H.property.1)) •
    F ((H.val.extractedOuter r H.property.2).graft (H.val.extractedInner r H.property.1) r
      (H.val.extractedChoices r H.property.2))
  rw [H.val.graft_extracted r H.property.1 H.property.2]

end EnvelopingIsomorphism.Deformation.GraphGeneralWeightedGraft

namespace EnvelopingIsomorphism.Deformation.KontsevichGraph.General.Graph

variable {a b m l : ℕ} {q : Fin a → ℕ} {p : Fin b → ℕ}

theorem extractedOuter_graft (Γ : Graph q (m + 1)) (Δ : Graph p (l + 1)) (r : Fin (m + 1))
    (χ : Γ.GraftChoices (b := b) (l := l) r) :
    (Γ.graft Δ r χ).extractedOuter r (graft_coarseDistinct r Γ Δ χ) = Γ :=
  congrArg (fun D : GraftData q p r l ↦ D.1) (extract_graft_data r ⟨Γ, Δ, χ⟩)

theorem extractedInner_graft (Γ : Graph q (m + 1)) (Δ : Graph p (l + 1)) (r : Fin (m + 1))
    (χ : Γ.GraftChoices (b := b) (l := l) r) :
    (Γ.graft Δ r χ).extractedInner r (graft_innerClosed r Γ Δ χ) = Δ :=
  congrArg (fun D : GraftData q p r l ↦ D.2.1) (extract_graft_data r ⟨Γ, Δ, χ⟩)

/-- Heterogeneous equality is required only because choices are indexed by
their outer graph; the preceding theorem identifies that recovered graph. -/
theorem extractedChoices_graft_heq (Γ : Graph q (m + 1)) (Δ : Graph p (l + 1)) (r : Fin (m + 1))
    (χ : Γ.GraftChoices (b := b) (l := l) r) :
    HEq ((Γ.graft Δ r χ).extractedChoices r (graft_coarseDistinct r Γ Δ χ)) χ :=
  congr_arg_heq (fun D : GraftData q p r l ↦ D.2.2) (extract_graft_data r ⟨Γ, Δ, χ⟩)

end EnvelopingIsomorphism.Deformation.KontsevichGraph.General.Graph
