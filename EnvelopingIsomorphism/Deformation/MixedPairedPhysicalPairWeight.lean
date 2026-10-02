import EnvelopingIsomorphism.Deformation.MixedPairedEdgeRelabelling
import EnvelopingIsomorphism.Deformation.MixedGraphOutgoingPairNormalization
import EnvelopingIsomorphism.Deformation.MixedPhysicalPairCoefficientRelabelling

/-! Reduction of literal arbitrary mixed two-point integrals to genuine
adjacent marked source and exterior-vector correction representatives. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.MixedPairedPhysicalPairWeight
open Kontsevich KontsevichGraph.General MixedGraphProfileCarrier MixedGraphAveraging
open MixedGraphPairLabelCounting MixedGraphCorrectionProfiles
open GraphCurvatureLabelCounting MixedPairedEdgeRelabelling TwoPointBinaryFaceAdmissibility
open scoped Classical BigOperators

theorem outgoingFactor_oneVector {N : ℕ} (v : Fin (N+1)) :
    GeometricWeights.outgoingFactor (Gauge.PlacedMixedGraphTaylorCoefficients.arities 1 v) =
      ((2 : ℝ)^N)⁻¹ := by
  unfold GeometricWeights.outgoingFactor
  rw [Fin.prod_univ_succAbove _ v]
  simp [Gauge.PlacedMixedGraphTaylorCoefficients.arities, Fin.succAbove_ne, ← inv_pow]

theorem normalization_eq {N : ℕ} (H : VectorGraph N 2) :
    normalization H = ((2 : ℝ)^N)⁻¹ * ((2 * Real.pi) ^ (GraphForms.dimension N 1))⁻¹ := by
  rw [normalization, outgoingFactor_oneVector]

theorem cluster_eq_childPair {n : ℕ} (v : Fin (n+1)) : cluster v = childPair v := by
  ext j
  simp [cluster, childPair, Fin.exists_fin_two, eq_comm]

section Source
variable {n : ℕ} (H : VectorGraph (n+1) 2) (T : PhysicalPair n)

def sourceRepresentative (hv : H.vertex ∈ T.val) : SourcePairLabels T H.vertex :=
  Classical.choice (Fintype.card_pos_iff.mp (by
    rw [card_sourcePairLabels T H.vertex hv]
    exact Nat.factorial_pos _))

variable (D : SourcePairLabels T H.vertex)

theorem source_cluster (j : Fin (n+2)) :
    D.2.val.val.symm j ∈ cluster D.1 ↔ j ∈ T.val := by
  rw [cluster_eq_childPair]
  have h := D.2.val.property (D.2.val.val.symm j)
  simpa only [Equiv.apply_symm_apply] using h.symm

theorem source_vertex :
    (internalGraphEquiv D.2.val.val.symm 2 H).vertex = vertexSplitChild D.1 0 := by
  rw [internalGraphEquiv_vertex]
  apply D.2.val.val.injective
  rw [Equiv.apply_symm_apply, D.2.property]

theorem sourceCoefficient_representative :
    MixedGraphOutgoingPairNormalization.sourcePhysicalCoefficient
      (internalGraphEquiv D.2.val.val.symm 2 H) ⟨cluster D.1,cluster_card D.1⟩ =
      MixedGraphOutgoingPairNormalization.sourcePhysicalCoefficient H T :=
  MixedPhysicalPairCoefficientRelabelling.sourcePhysicalCoefficient_internal _ H T _
    (source_cluster H T D)

variable {i a b : Fin (n+2)} (ha : a ∈ T.val) (hb : b ∈ T.val)
  (hba : b ≠ a) (hi : i ∈ T.val → a = i)

/-- Transport to an actual representative fixes the vector at the first
child, retains the moved global anchor and preserves the whole integral. -/
theorem normalized_sourceRepresentative :
    normalized ha hb hba hi H =
      normalized ((source_cluster H T D a).mpr ha) ((source_cluster H T D b).mpr hb)
        (D.2.val.val.symm.injective.ne hba)
        (anchor_relabel hi D.2.val.val.symm (source_cluster H T D))
        (internalGraphEquiv D.2.val.val.symm 2 H) :=
  (normalized_relabel ha hb hba hi D.2.val.val.symm (source_cluster H T D) H T.property).symm
end Source

section Correction
variable {n : ℕ} (H : VectorGraph (n+2) 2) (T : PhysicalPair (n+1))

def correctionRepresentative (hv : H.vertex ∉ T.val) : CorrectionPairLabels T H.vertex :=
  Classical.choice (Fintype.card_pos_iff.mp (by
    rw [card_correctionPairLabels T H.vertex hv]
    exact Nat.mul_pos (by decide) (Nat.factorial_pos _)))

variable (D : CorrectionPairLabels T H.vertex)

theorem correction_cluster (j : Fin (n+3)) :
    D.2.val.val.symm j ∈ cluster D.1.2.val ↔ j ∈ T.val := by
  rw [cluster_eq_childPair]
  have h := D.2.val.property (D.2.val.val.symm j)
  simpa only [Equiv.apply_symm_apply] using h.symm

theorem correction_vertex :
    (internalGraphEquiv D.2.val.val.symm 2 H).vertex = expandedVector D.1 := by
  rw [internalGraphEquiv_vertex]
  apply D.2.val.val.injective
  rw [Equiv.apply_symm_apply, D.2.property]

theorem correctionCoefficient_representative :
    MixedGraphOutgoingPairNormalization.correctionPhysicalCoefficient
      (internalGraphEquiv D.2.val.val.symm 2 H) ⟨cluster D.1.2.val,cluster_card D.1.2.val⟩ =
      MixedGraphOutgoingPairNormalization.correctionPhysicalCoefficient H T :=
  MixedPhysicalPairCoefficientRelabelling.correctionPhysicalCoefficient_internal _ H T _
    (correction_cluster H T D)

variable {i a b : Fin (n+3)} (ha : a ∈ T.val) (hb : b ∈ T.val)
  (hba : b ≠ a) (hi : i ∈ T.val → a = i)

/-- The retained exterior vector is transported along with the physical
pair. No quotient placement sign is discarded by this integral equality. -/
theorem normalized_correctionRepresentative :
    normalized ha hb hba hi H =
      normalized ((correction_cluster H T D a).mpr ha) ((correction_cluster H T D b).mpr hb)
        (D.2.val.val.symm.injective.ne hba)
        (anchor_relabel hi D.2.val.val.symm (correction_cluster H T D))
        (internalGraphEquiv D.2.val.val.symm 2 H) :=
  (normalized_relabel ha hb hba hi D.2.val.val.symm (correction_cluster H T D) H T.property).symm
end Correction

end EnvelopingIsomorphism.Deformation.MixedPairedPhysicalPairWeight
