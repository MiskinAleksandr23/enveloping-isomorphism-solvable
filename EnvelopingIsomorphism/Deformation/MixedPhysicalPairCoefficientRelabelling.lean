import EnvelopingIsomorphism.Deformation.MixedGraphOutgoingPairNormalization
import EnvelopingIsomorphism.Deformation.MixedGraphGraftOutgoing

/-! Covariance of the literal mixed physical-pair coefficients, with the
distinguished vector and every native outgoing row transported together. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
namespace EnvelopingIsomorphism.Deformation.MixedPhysicalPairCoefficientRelabelling
open scoped Classical BigOperators
open KontsevichGraph.General GraphCurvatureLabelCounting
open MixedGraphAveraging MixedGraphProfileCarrier MixedGraphBlockRelabelling
open MixedGraphPairLabelCounting MixedGraphPhysicalPairSums MixedGraphOutgoingPairNormalization
open MixedGraphTargetProfiles
variable {n : ℕ}

def sourceLabelsMap (σ : Equiv.Perm (Fin (n+2))) (T U : PhysicalPair n)
    (hTU : ∀ j, σ j ∈ U.val ↔ j ∈ T.val) (v : Fin (n+2))
    (D : SourcePairLabels T v) : SourcePairLabels U (σ v) :=
  ⟨D.1, ⟨⟨D.2.val.val.trans σ, fun j ↦ (hTU _).trans (D.2.val.property j)⟩,
    congrArg σ D.2.property⟩⟩

def correctionLabelsMap (σ : Equiv.Perm (Fin (n+3))) (T U : PhysicalPair (n+1))
    (hTU : ∀ j, σ j ∈ U.val ↔ j ∈ T.val) (v : Fin (n+3))
    (D : CorrectionPairLabels T v) : CorrectionPairLabels U (σ v) :=
  ⟨D.1, ⟨⟨D.2.val.val.trans σ, fun j ↦ (hTU _).trans (D.2.val.property j)⟩,
    congrArg σ D.2.property⟩⟩

theorem inverse_composite_internal {N m : ℕ} (σ τ : Equiv.Perm (Fin (N+1)))
    (H : VectorGraph N m) :
    (internalGraphEquiv (τ.trans σ) m).symm (internalGraphEquiv σ m H) =
      (internalGraphEquiv τ m).symm H := by
  apply (internalGraphEquiv (τ.trans σ) m).injective
  rw [Equiv.apply_symm_apply, ← internalGraphEquiv_trans, Equiv.apply_symm_apply]

theorem rawSourcePairCoefficient_internal (σ : Equiv.Perm (Fin (n+2)))
    (H : VectorGraph (n+1) 2) (T U : PhysicalPair n)
    (hTU : ∀ j, σ j ∈ U.val ↔ j ∈ T.val) :
    rawSourcePairCoefficient (internalGraphEquiv σ 2 H) U = rawSourcePairCoefficient H T := by
  by_cases hv : H.vertex ∈ T.val
  · obtain ⟨D⟩ := Fintype.card_pos_iff.mp (show 0 < Fintype.card (SourcePairLabels T H.vertex) by
      rw [card_sourcePairLabels T H.vertex hv]
      exact Nat.factorial_pos _)
    rw [rawSourcePairCoefficient_eq H T D,
      rawSourcePairCoefficient_eq _ U (sourceLabelsMap σ T U hTU H.vertex D)]
    dsimp only [sourceLabelsMap]
    rw [inverse_composite_internal]
  · have hu : (internalGraphEquiv σ 2 H).vertex ∉ U.val := fun h ↦ hv ((hTU _).mp h)
    simp only [rawSourcePairCoefficient, dif_neg hv, dif_neg hu]

theorem rawCorrectionPairCoefficient_internal (σ : Equiv.Perm (Fin (n+3)))
    (H : VectorGraph (n+2) 2) (T U : PhysicalPair (n+1))
    (hTU : ∀ j, σ j ∈ U.val ↔ j ∈ T.val) :
    rawCorrectionPairCoefficient (internalGraphEquiv σ 2 H) U = rawCorrectionPairCoefficient H T := by
  by_cases hv : H.vertex ∉ T.val
  · obtain ⟨D⟩ := Fintype.card_pos_iff.mp (show 0 < Fintype.card (CorrectionPairLabels T H.vertex) by
      rw [card_correctionPairLabels T H.vertex hv]
      exact Nat.mul_pos (by decide) (Nat.factorial_pos _))
    rw [rawCorrectionPairCoefficient_eq_scaled H T D,
      rawCorrectionPairCoefficient_eq_scaled _ U (correctionLabelsMap σ T U hTU H.vertex D)]
    dsimp only [correctionLabelsMap]
    rw [inverse_composite_internal]
  · have hu : ¬(internalGraphEquiv σ 2 H).vertex ∉ U.val := fun h ↦ hv (fun ht ↦ h ((hTU _).mpr ht))
    simp only [rawCorrectionPairCoefficient, dif_neg hv, dif_neg hu]

theorem arity_relabel {N : ℕ} (σ : Equiv.Perm (Fin (N+1))) (i v : Fin (N+1)) :
    Gauge.PlacedMixedGraphTaylorCoefficients.arities 1 i v =
      Gauge.PlacedMixedGraphTaylorCoefficients.arities 1 (σ i) (σ v) := by
  simp [Gauge.PlacedMixedGraphTaylorCoefficients.arities, σ.injective.eq_iff]

def nativeOutgoingEquiv {N : ℕ} (σ : Equiv.Perm (Fin (N+1))) (i : Fin (N+1)) :
    FullOutgoing i ≃ FullOutgoing (σ i) :=
  σ.piCongr (fun v ↦ (finCongr (arity_relabel σ i v)).permCongr)

theorem nativeOutgoingEquiv_apply {N : ℕ} (σ : Equiv.Perm (Fin (N+1))) (i v : Fin (N+1))
    (α : FullOutgoing i) :
    nativeOutgoingEquiv σ i α (σ v) = (finCongr (arity_relabel σ i v)).permCongr (α v) :=
  Equiv.piCongr_apply_apply _ _ _ _

theorem nativeOutgoingEquiv_sign {N : ℕ} (σ : Equiv.Perm (Fin (N+1))) (i : Fin (N+1))
    (α : FullOutgoing i) :
    (∏ v, permutationSign (R := ℝ) (nativeOutgoingEquiv σ i α v)) =
      ∏ v, permutationSign (R := ℝ) (α v) := by
  rw [← Equiv.prod_comp σ (fun v ↦ permutationSign (R := ℝ) (nativeOutgoingEquiv σ i α v))]
  simp only [nativeOutgoingEquiv_apply, permutationSign, Equiv.Perm.sign_permCongr]

theorem internal_permuteOutgoing {N m : ℕ} (σ : Equiv.Perm (Fin (N+1)))
    (H : VectorGraph N m) (α : FullOutgoing H.vertex) :
    internalGraphEquiv σ m ⟨H.vertex,H.graph.permuteOutgoing α⟩ =
      ⟨σ H.vertex,(internalGraphEquiv σ m H).graph.permuteOutgoing (nativeOutgoingEquiv σ H.vertex α)⟩ := by
  let F := vectorRelabelling σ H
  have h : ∀ v, vectorArity H.vertex v = vectorArity (σ H.vertex) (F.vertices v) := by
    intro v
    rw [show F.vertices = σ from vectorRelabelling_vertices σ H]
    exact arity_relabel σ H.vertex v
  have hp : F.pullOutgoing h (nativeOutgoingEquiv σ H.vertex α) = α := by
    have he : F.vertices.piCongr (fun v ↦ (finCongr (h v)).permCongr) =
        nativeOutgoingEquiv σ H.vertex := by
      generalize hv : F.vertices = π at h ⊢
      have hπ : π = σ := hv.symm.trans (vectorRelabelling_vertices σ H)
      clear hv
      subst π
      rfl
    change (F.vertices.piCongr (fun v ↦ (finCongr (h v)).permCongr)).symm
      (nativeOutgoingEquiv σ H.vertex α) = α
    rw [he, Equiv.symm_apply_apply]
  have he := vectorGraph_eq_internal
    (Γ := ⟨H.vertex, H.graph.permuteOutgoing (F.pullOutgoing h (nativeOutgoingEquiv σ H.vertex α))⟩)
    (Δ := ⟨σ H.vertex, (internalGraphEquiv σ m H).graph.permuteOutgoing (nativeOutgoingEquiv σ H.vertex α)⟩)
    σ (F.permuteOutgoing h (nativeOutgoingEquiv σ H.vertex α)) (vectorRelabelling_vertices σ H) rfl
  rw [hp] at he
  exact he.symm

theorem outgoingAverage_internal {N : ℕ} (σ : Equiv.Perm (Fin (N+1)))
    (c d : VectorGraph N 2 → ℝ) (hc : ∀ H, d (internalGraphEquiv σ 2 H) = c H)
    (H : VectorGraph N 2) :
    outgoingAverage d (internalGraphEquiv σ 2 H) = outgoingAverage c H := by
  rw [outgoingAverage_eq_full_forward, outgoingAverage_eq_full_forward]
  congr 1
  symm
  apply Fintype.sum_equiv (nativeOutgoingEquiv σ H.vertex)
  intro α
  rw [nativeOutgoingEquiv_sign]
  congr 1
  exact (hc _).symm.trans (congrArg d (internal_permuteOutgoing σ H α))

theorem sourcePhysicalCoefficient_internal (σ : Equiv.Perm (Fin (n+2)))
    (H : VectorGraph (n+1) 2) (T U : PhysicalPair n)
    (hTU : ∀ j, σ j ∈ U.val ↔ j ∈ T.val) :
    sourcePhysicalCoefficient (internalGraphEquiv σ 2 H) U = sourcePhysicalCoefficient H T := by
  have h := outgoingAverage_internal σ
    (fun H ↦ rawSourcePairCoefficient H T) (fun H ↦ rawSourcePairCoefficient H U)
    (fun H ↦ rawSourcePairCoefficient_internal σ H T U hTU) H
  simpa only [sourcePhysicalCoefficient, outgoingAverage_apply] using h

theorem correctionPhysicalCoefficient_internal (σ : Equiv.Perm (Fin (n+3)))
    (H : VectorGraph (n+2) 2) (T U : PhysicalPair (n+1))
    (hTU : ∀ j, σ j ∈ U.val ↔ j ∈ T.val) :
    correctionPhysicalCoefficient (internalGraphEquiv σ 2 H) U = correctionPhysicalCoefficient H T := by
  have h := congrArg (fun c : ℝ ↦ 2*c) (outgoingAverage_internal σ
    (fun H ↦ rawCorrectionPairCoefficient H T) (fun H ↦ rawCorrectionPairCoefficient H U)
    (fun H ↦ rawCorrectionPairCoefficient_internal σ H T U hTU) H)
  simpa only [correctionPhysicalCoefficient, outgoingAverage_apply, mul_assoc] using h

theorem sourcePhysicalCoefficient_zero_of_vector_not_mem
    (H : VectorGraph (n+1) 2) (T : PhysicalPair n) (hv : H.vertex ∉ T.val) :
    sourcePhysicalCoefficient H T = 0 := by
  simp [sourcePhysicalCoefficient, rawSourcePairCoefficient,
    outgoingGraphEquiv_symm_carrier, VectorGraph.vertex, hv]

theorem correctionPhysicalCoefficient_zero_of_vector_mem
    (H : VectorGraph (n+2) 2) (T : PhysicalPair (n+1)) (hv : H.vertex ∈ T.val) :
    correctionPhysicalCoefficient H T = 0 := by
  simp [correctionPhysicalCoefficient, rawCorrectionPairCoefficient,
    outgoingGraphEquiv_symm_carrier, VectorGraph.vertex, hv]

end EnvelopingIsomorphism.Deformation.MixedPhysicalPairCoefficientRelabelling
