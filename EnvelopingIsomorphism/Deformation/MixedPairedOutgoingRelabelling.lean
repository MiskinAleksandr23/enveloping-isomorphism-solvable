import EnvelopingIsomorphism.Deformation.MixedPairedEdgeRelabelling
import EnvelopingIsomorphism.Deformation.Kontsevich.GeometricWeightOutgoing

/-! Actual normalized mixed pair-face integrals under every native outgoing
slot permutation, including sender-slot normalization at an interior pair. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.MixedPairedOutgoingRelabelling
open Kontsevich KontsevichGraph.General MixedGraphProfileCarrier MixedGraphAveraging
open MixedScalarBoundaryAssembly MixedPairedEdgeRelabelling InteriorGraphFaceCoordinates
open scoped Classical BigOperators
variable {N : ℕ} (H : VectorGraph N 2)
  (τ : (v : Fin (N+1)) → Equiv.Perm (Fin (Gauge.PlacedMixedGraphTaylorCoefficients.arities 1 H.vertex v)))

def permuted : VectorGraph N 2 := ⟨H.vertex,H.graph.permuteOutgoing τ⟩

def rows : Equiv.Perm (Fin (GraphForms.dimension N 1)) :=
  GeometricWeightOutgoing.orderPermutation
    (GeometricWeights.canonicalOrder (Gauge.PlacedMixedGraphTaylorCoefficients.edgeCount 1 H.vertex)) τ

theorem rows_sign : (rows H τ).sign = ∏ v, Equiv.Perm.sign (τ v) :=
  GeometricWeightOutgoing.orderPermutation_sign _ τ

theorem mixedEdges_permuted : mixedEdges (permuted H τ) = fun j => mixedEdges H (rows H τ j) := by
  funext j
  unfold mixedEdges permuted rows GeometricWeightOutgoing.orderPermutation
  simp only [Equiv.trans_apply, Equiv.apply_symm_apply]
  rfl

variable {i a b : Fin (N+1)} {S : Finset (Fin (N+1))}
  (ha : a ∈ S) (hb : b ∈ S) (hba : b ≠ a) (hi : i ∈ S → a = i)

def nativeRows : Equiv.Perm (Fin (shapeDegree a b S + coarseDegree i a S 2)) :=
  (finCongr (nativeDegree_eq ha hb hba hi)).symm.permCongr (rows H τ)

theorem nativeRows_sign : ((nativeRows H τ ha hb hba hi).sign : ℝ) =
    ∏ v, permutationSign (R := ℝ) (τ v) := by
  rw [nativeRows, Equiv.Perm.sign_permCongr, rows_sign]
  let f : ℤˣ →* ℝ := (Int.castRingHom ℝ).toMonoidHom.comp (Units.coeHom ℤ)
  exact map_prod f _ Finset.univ

theorem nativeEdges_permuted :
    nativeEdges ha hb hba hi (permuted H τ) =
      fun j => nativeEdges ha hb hba hi H (nativeRows H τ ha hb hba hi j) := by
  funext j
  unfold nativeEdges
  rw [mixedEdges_permuted]
  unfold nativeRows Equiv.permCongr
  dsimp only [Equiv.trans_apply]
  congr 2

theorem integral_permuted :
    TwoPointFaceRelabelling.integral (nativeEdges ha hb hba hi (permuted H τ)) =
      (∏ v, permutationSign (R := ℝ) (τ v)) *
        TwoPointFaceRelabelling.integral (nativeEdges ha hb hba hi H) := by
  rw [nativeEdges_permuted, TwoPointFaceRelabelling.integral_permute, nativeRows_sign]

theorem normalized_permuted :
    normalized ha hb hba hi (permuted H τ) =
      (∏ v, permutationSign (R := ℝ) (τ v)) * normalized ha hb hba hi H := by
  unfold normalized
  rw [integral_permuted]
  have he : normalization (permuted H τ) = normalization H := rfl
  rw [he]
  ring

theorem normalized_outgoingGraphEquiv (ρ : OutgoingGroup N) :
    normalized ha hb hba hi (outgoingGraphEquiv ρ 2 H) =
      outgoingSign (k := ℝ) ρ * normalized ha hb hba hi H := by
  have h := normalized_permuted H (outgoingAt H.vertex ρ) ha hb hba hi
  rw [outgoingAt_sign_prod] at h
  exact h

end EnvelopingIsomorphism.Deformation.MixedPairedOutgoingRelabelling
