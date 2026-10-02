import EnvelopingIsomorphism.Deformation.BinaryGraphAveraging

/-! Exact signed covariance of the literal binary outgoing average. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.BinaryGraphAveraging
open UniformBinaryGraphs KontsevichGraph.General
open scoped Classical BigOperators
variable {n : ℕ} {k : Type*} [Field k]

theorem outgoingSign_mul (σ τ : Fin n → Equiv.Perm (Fin 2)) :
    outgoingSign (k := k) (σ * τ) = outgoingSign σ * outgoingSign τ := by
  simp [outgoingSign, permutationSign, Equiv.Perm.sign_mul, Finset.prod_mul_distrib]

theorem permuteOutgoing_cancel_right (H : BinaryGraph n 3)
    (σ τ : Fin n → Equiv.Perm (Fin 2)) :
    (H.permuteOutgoing σ).permuteOutgoing (fun v ↦ ((τ * σ) v).symm) =
      H.permuteOutgoing (fun v ↦ (τ v).symm) := by
  apply Graph.ext
  funext e
  rcases e with ⟨v,j⟩
  change H.target ⟨v,σ v (((τ v) * (σ v)).symm j)⟩ = H.target ⟨v,(τ v).symm j⟩
  congr 2
  apply (τ v).injective
  change ((τ v) * (σ v)) (((τ v) * (σ v)).symm j) = (τ v) ((τ v).symm j)
  simp

/-- Reindexing the finite averaging permutations gives the exact outgoing
sign on any coefficient table, including graph tables with zero fibres. -/
theorem outgoingAverage_permuteOutgoing (c : BinaryGraph n 3 → k)
    (H : BinaryGraph n 3) (σ : Fin n → Equiv.Perm (Fin 2)) :
    outgoingAverage c (H.permuteOutgoing σ) = outgoingSign σ * outgoingAverage c H := by
  rw [outgoingAverage_apply, outgoingAverage_apply]
  rw [← Equiv.sum_comp (Equiv.mulRight σ)]
  change ((2 : k)^n)⁻¹ * (∑ τ : Fin n → Equiv.Perm (Fin 2), outgoingSign (τ * σ) *
    c ((H.permuteOutgoing σ).permuteOutgoing (fun v ↦ ((τ * σ) v).symm))) = _
  simp only [permuteOutgoing_cancel_right, outgoingSign_mul]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro τ _
  ring

end EnvelopingIsomorphism.Deformation.BinaryGraphAveraging
