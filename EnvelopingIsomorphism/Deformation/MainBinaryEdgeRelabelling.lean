import EnvelopingIsomorphism.Deformation.MainScalarBoundaryAssembly
import EnvelopingIsomorphism.Deformation.Kontsevich.GeometricWeightRelabel

/-! Internal vertex relabelling of the original main edge array has an
explicit even permutation of its binary outgoing blocks. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.MainBinaryEdgeRelabelling
open MainScalarBoundaryAssembly UniformBinaryGraphs Kontsevich
open KontsevichGraph.General
open scoped Classical
variable {n : ℕ} (σ : Equiv.Perm (Fin (n+2)))

def rows : Equiv.Perm (Fin (GraphForms.dimension (n+1) 2)) :=
  GeometricWeights.canonicalProfileRows (GeometricWeights.binaryEdgeCount (n+1)) σ

theorem rows_sign : (rows σ).sign = 1 := by
  rw [rows, GeometricWeights.canonicalProfileRows_sign]
  exact profileRowPerm_sign_eq_one_of_even _ σ (fun _ ↦ by decide)

theorem mainEdges_permuteInternal (H : BinaryGraph (n+2) 3) :
    mainEdges (H.permuteInternal σ) =
      fun j ↦ GeometricWeights.relabelEdge σ (mainEdges H (rows σ j)) := by
  funext j
  have ho := congrArg (fun e ↦ e j)
    (GeometricWeights.canonicalOrder_permuteProfile
      (GeometricWeights.binaryEdgeCount (n+1)) σ)
  change GeometricWeights.canonicalOrder (GeometricWeights.binaryEdgeCount (n+1)) j =
    profileEdgeEquiv (fun _ : Fin (n+2) ↦ 2) σ
      (GeometricWeights.canonicalOrder (GeometricWeights.binaryEdgeCount (n+1)) (rows σ j)) at ho
  unfold mainEdges
  rw [ho]
  simp only [GeometricWeights.relabelEdge]
  congr 1
  have hp : profileEdgeEquiv (fun _ : Fin (n+2) ↦ 2) σ = internalEdgePerm 2 σ := by
    apply Equiv.ext
    intro e
    apply Sigma.ext
    · exact profileEdgeEquiv_source _ σ e
    · apply heq_of_eq
      apply Fin.ext
      exact profileEdgeEquiv_slot_val _ σ e
  rw [hp]
  refine (H.permuteInternal_target σ _).trans ?_
  cases H.target (GeometricWeights.canonicalOrder
    (GeometricWeights.binaryEdgeCount (n+1)) (rows σ j)) <;> rfl

end EnvelopingIsomorphism.Deformation.MainBinaryEdgeRelabelling
