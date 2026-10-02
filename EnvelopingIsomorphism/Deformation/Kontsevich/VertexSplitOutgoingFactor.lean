import EnvelopingIsomorphism.Deformation.Kontsevich.GeometricWeights
import EnvelopingIsomorphism.Deformation.GeneralGraphVertexSplitConstruction
import EnvelopingIsomorphism.Deformation.SchoutenGraphVertexSplit

/-! The genuine factorial ratio for splitting one vertex, with arbitrary
background arities, including a retained vector vertex. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Kontsevich.VertexSplitOutgoingFactor

open KontsevichGraph.General KontsevichGraph.General.TwoVertexContraction
open scoped Classical BigOperators

variable {n : ℕ} (q : Fin (n + 1) → ℕ) (r : Fin (n + 1))

def outsideFactor : ℝ :=
  ∏ v : {v : Fin (n + 1) // v ≠ r}, ((q v.val).factorial : ℝ)⁻¹

theorem outgoingFactor_eq : GeometricWeights.outgoingFactor q =
    ((q r).factorial : ℝ)⁻¹ * outsideFactor q r := by
  unfold GeometricWeights.outgoingFactor outsideFactor
  rw [← Finset.prod_subtype (p := fun v : Fin (n + 1) => v ≠ r)
    (Finset.univ.erase r) (by simp) (fun v => ((q v).factorial : ℝ)⁻¹)]
  exact (Finset.mul_prod_erase Finset.univ (fun v => ((q v).factorial : ℝ)⁻¹)
    (Finset.mem_univ r)).symm

theorem split_outgoingFactor_eq (qLocal : Fin 2 → ℕ) :
    GeometricWeights.outgoingFactor (vertexSplitArity q qLocal r) =
      outsideFactor q r *
        (((qLocal 0).factorial : ℝ)⁻¹ * ((qLocal 1).factorial : ℝ)⁻¹) := by
  unfold GeometricWeights.outgoingFactor
  rw [← Equiv.prod_comp (vertexSplitSourceEquiv r).symm]
  simp [vertexSplitArity, Fintype.prod_sum_type, outsideFactor, Fin.prod_univ_two]
  ring

theorem bivector_split_factor (hq : q r = 3) :
    GeometricWeights.outgoingFactor (vertexSplitArity q bivectorArity r) =
      (3 / 2 : ℝ) * GeometricWeights.outgoingFactor q := by
  rw [split_outgoingFactor_eq, outgoingFactor_eq, hq]
  norm_num [bivectorArity]
  ring

theorem vector_bivector_split_factor (hq : q r = 2) :
    GeometricWeights.outgoingFactor (vertexSplitArity q vectorBivectorArity r) =
      GeometricWeights.outgoingFactor q := by
  rw [split_outgoingFactor_eq, outgoingFactor_eq, hq]
  norm_num [vectorBivectorArity]
  ring

end EnvelopingIsomorphism.Deformation.Kontsevich.VertexSplitOutgoingFactor
