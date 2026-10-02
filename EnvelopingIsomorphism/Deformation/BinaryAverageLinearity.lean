import EnvelopingIsomorphism.Deformation.BinaryOutgoingAverageCovariance

/-! Linearity and exact commutation of the actual internal and outgoing
binary graph averages, by reindexing their genuine graph permutations. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.BinaryGraphAveraging
open UniformBinaryGraphs KontsevichGraph.General
open scoped Classical BigOperators
variable {n : ℕ} {k : Type*} [Field k]

theorem outgoingAverage_smul (s : k) (c : BinaryGraph n 3 → k) :
    outgoingAverage (s • c) = s • outgoingAverage c := by
  funext H
  simp only [outgoingAverage_apply, Pi.smul_apply, smul_eq_mul]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro τ _
  ring

theorem outgoingAverage_sum {J : Type*} [Fintype J] (c : J → BinaryGraph n 3 → k) :
    outgoingAverage (∑ j, c j) = ∑ j, outgoingAverage (c j) := by
  funext H
  simp only [outgoingAverage_apply, Finset.sum_apply, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem internalAverage_sum {J : Type*} [Fintype J] (c : J → BinaryGraph n 3 → k) :
    internalAverage (∑ j, c j) = ∑ j, internalAverage (c j) := by
  funext H
  simp only [internalAverage_apply, Finset.sum_apply, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem outgoingSign_reindex (τ : Fin n → Equiv.Perm (Fin 2)) (σ : Equiv.Perm (Fin n)) :
    outgoingSign (k := k) (fun v ↦ τ (σ v)) = outgoingSign τ :=
  Equiv.prod_comp σ (fun v ↦ permutationSign (R := k) (τ v))

theorem permuteOutgoing_internal (H : BinaryGraph n 3)
    (τ : Fin n → Equiv.Perm (Fin 2)) (σ : Equiv.Perm (Fin n)) :
    (H.permuteOutgoing (fun v ↦ (τ v).symm)).permuteInternal σ.symm =
      (H.permuteInternal σ.symm).permuteOutgoing (fun v ↦ (τ (σ v)).symm) := by
  apply Graph.ext
  funext e
  rcases e with ⟨v,j⟩
  rfl

/-- The two finite sums differ only by the genuine action of the internal
vertex permutation on the indices of the outgoing permutations. -/
theorem sum_outgoing_internal_commute (c : BinaryGraph n 3 → k)
    (H : BinaryGraph n 3) (σ : Equiv.Perm (Fin n)) :
    (∑ τ : Fin n → Equiv.Perm (Fin 2), outgoingSign τ *
      c ((H.permuteOutgoing (fun v ↦ (τ v).symm)).permuteInternal σ.symm)) =
    ∑ τ : Fin n → Equiv.Perm (Fin 2), outgoingSign τ *
      c ((H.permuteInternal σ.symm).permuteOutgoing (fun v ↦ (τ v).symm)) := by
  let e : Equiv.Perm (Fin n → Equiv.Perm (Fin 2)) := Equiv.arrowCongr σ.symm (Equiv.refl _)
  conv_rhs => rw [← Equiv.sum_comp e]
  apply Finset.sum_congr rfl
  intro τ _
  change outgoingSign τ * c ((H.permuteOutgoing (fun v ↦ (τ v).symm)).permuteInternal σ.symm) =
    outgoingSign (fun v ↦ τ (σ v)) * c ((H.permuteInternal σ.symm).permuteOutgoing (fun v ↦ (τ (σ v)).symm))
  rw [outgoingSign_reindex, permuteOutgoing_internal]

/-- Internal and signed outgoing averaging commute on every scalar table. -/
theorem outgoingAverage_internalAverage (c : BinaryGraph n 3 → k) :
    outgoingAverage (internalAverage c) = internalAverage (outgoingAverage c) := by
  funext H
  simp only [outgoingAverage_apply, internalAverage_apply]
  change ((2 : k)^n)⁻¹ * (∑ τ, outgoingSign τ * ((n.factorial : k)⁻¹ *
      ∑ σ : Equiv.Perm (Fin n), c ((H.permuteOutgoing (fun v ↦ (τ v).symm)).permuteInternal σ.symm))) =
    (n.factorial : k)⁻¹ * ∑ σ : Equiv.Perm (Fin n), ((2 : k)^n)⁻¹ *
      ∑ τ, outgoingSign τ * c ((H.permuteInternal σ.symm).permuteOutgoing (fun v ↦ (τ v).symm))
  have he : (∑ τ, outgoingSign (k := k) τ * ((n.factorial : k)⁻¹ *
      ∑ σ : Equiv.Perm (Fin n), c ((H.permuteOutgoing (fun v ↦ (τ v).symm)).permuteInternal σ.symm))) =
      (n.factorial : k)⁻¹ * ∑ σ : Equiv.Perm (Fin n), ∑ τ,
        outgoingSign τ * c ((H.permuteOutgoing (fun v ↦ (τ v).symm)).permuteInternal σ.symm) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro σ _
    apply Finset.sum_congr rfl
    intro τ _
    ring
  rw [he]
  simp only [sum_outgoing_internal_commute, ← Finset.mul_sum]
  ring

end EnvelopingIsomorphism.Deformation.BinaryGraphAveraging
