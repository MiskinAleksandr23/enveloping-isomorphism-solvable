import EnvelopingIsomorphism.Deformation.BinaryGraphAveraging
import Mathlib.Data.Finset.Powerset

/-! Exact label multiplicities for boundary clusters. A permutation carrying one
internal cluster to another is precisely a pair of bijections on the cluster
and its complement. Empty and full clusters are included. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Classical
namespace EnvelopingIsomorphism.Deformation.GraphLabelledClusterCounting

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Permutations carrying the first cluster onto the second, in pointwise form. -/
abbrev ClusterFiber (S T : Finset α) :=
  {σ : Equiv.Perm α // ∀ x, σ x ∈ T ↔ x ∈ S}

/-- Restricting to a cluster and its complement accounts for every label exactly once. -/
def clusterFiberEquiv (S T : Finset α) :
    ClusterFiber S T ≃ (S ≃ T) × ({x // x ∉ S} ≃ {x // x ∉ T}) where
  toFun σ := (Equiv.subtypeEquiv σ.val (fun x ↦ (σ.property x).symm),
    Equiv.subtypeEquiv σ.val (fun x ↦ not_congr (σ.property x).symm))
  invFun e := ⟨Equiv.subtypeCongr e.1 e.2, by
    intro x
    by_cases hx : x ∈ S
    · simp [Equiv.subtypeCongr, Equiv.sumCompl_symm_apply_of_pos hx, (e.1 ⟨x, hx⟩).property, hx]
    · simp [Equiv.subtypeCongr, Equiv.sumCompl_symm_apply_of_neg hx, (e.2 ⟨x, hx⟩).property, hx]⟩
  left_inv σ := by
    apply Subtype.ext
    apply Equiv.ext
    intro x
    by_cases hx : x ∈ S <;> simp [Equiv.subtypeCongr, hx]
  right_inv e := by
    apply Prod.ext <;> apply Equiv.ext <;> intro x <;> apply Subtype.ext
    · simp [Equiv.subtypeCongr, x.property]
    · simp [Equiv.subtypeCongr, x.property]

/-- The true label multiplicity, retaining both independent factorials. -/
theorem card_clusterFiber (S T : Finset α) (h : S.card = T.card) :
    Fintype.card (ClusterFiber S T) = S.card.factorial * (Fintype.card α - S.card).factorial := by
  let e : S ≃ T := Finset.equivOfCardEq h
  have hc : Fintype.card {x // x ∉ S} = Fintype.card {x // x ∉ T} := by
    simp only [Fintype.card_subtype_compl, Fintype.card_coe, h]
  let ec : {x // x ∉ S} ≃ {x // x ∉ T} := Fintype.equivOfCardEq hc
  rw [Fintype.card_congr (clusterFiberEquiv S T), Fintype.card_prod,
    Fintype.card_equiv e, Fintype.card_equiv ec, Fintype.card_coe,
    Fintype.card_subtype_compl, Fintype.card_coe]

/-- Actual subsets of the same cardinality, without a chosen anchor. -/
abbrev Clusters (S : Finset α) := {T : Finset α // T.card = S.card}

def movedCluster (S : Finset α) (σ : Equiv.Perm α) : Clusters S :=
  ⟨S.map σ.toEmbedding, Finset.card_map _⟩

omit [Fintype α] [DecidableEq α] in
theorem movedCluster_eq_iff (S : Finset α) (σ : Equiv.Perm α) (T : Clusters S) :
    movedCluster S σ = T ↔ ∀ x, σ x ∈ T.val ↔ x ∈ S := by
  constructor
  · intro h x
    have he := congrArg Subtype.val h
    rw [← he]
    simp [movedCluster]
  · intro h
    apply Subtype.ext
    apply Finset.ext
    intro x
    simpa only [movedCluster, Finset.mem_map_equiv, Equiv.apply_symm_apply] using
      (h (σ.symm x)).symm

theorem card_movedCluster_fiber (S : Finset α) (T : Clusters S) :
    Fintype.card {σ : Equiv.Perm α // movedCluster S σ = T} =
      S.card.factorial * (Fintype.card α - S.card).factorial := by
  rw [Fintype.card_congr (Equiv.subtypeEquivRight (fun σ ↦ movedCluster_eq_iff S σ T))]
  exact card_clusterFiber S T.val T.property.symm

/-- A representative uses independent bijections on the cluster and its
complement. Subsequent invariance results make this choice immaterial. -/
def clusterRepresentative (S : Finset α) (T : Clusters S) : ClusterFiber S T.val :=
  (clusterFiberEquiv S T.val).symm
    ⟨Finset.equivOfCardEq T.property.symm,
      Fintype.equivOfCardEq (by simp only [Fintype.card_subtype_compl, Fintype.card_coe,
        T.property])⟩

/-- Every actual subset appears with precisely the two independent label
factorials. The formula also holds for the empty and full cluster. -/
theorem sum_permutations_eq_cluster_sum {k : Type*} [CommSemiring k]
    (S : Finset α) (f : Clusters S → k) :
    (∑ σ : Equiv.Perm α, f (movedCluster S σ)) =
      (S.card.factorial : k) * ((Fintype.card α - S.card).factorial : k) *
        ∑ T : Clusters S, f T := by
  rw [← Fintype.sum_fiberwise (movedCluster S) (fun σ ↦ f (movedCluster S σ))]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T hT
  have he : (∑ σ : {σ : Equiv.Perm α // movedCluster S σ = T},
      f (movedCluster S σ.val)) =
      (Fintype.card {σ : Equiv.Perm α // movedCluster S σ = T} : k) * f T := by
    calc
      _ = ∑ _σ : {σ : Equiv.Perm α // movedCluster S σ = T}, f T :=
        Finset.sum_congr rfl (fun σ _ ↦ congrArg f σ.property)
      _ = _ := by simp [nsmul_eq_mul]
  rw [he, card_movedCluster_fiber, Nat.cast_mul]

/-- The two MC factorials cancel exactly the independent internal relabellings. -/
theorem sum_normalized_permutations_eq_cluster_sum {k : Type*} [Field k] [CharZero k]
    (S : Finset α) (f : Clusters S → k) :
    (∑ σ : Equiv.Perm α,
      (S.card.factorial : k)⁻¹ * ((Fintype.card α - S.card).factorial : k)⁻¹ *
        f (movedCluster S σ)) = ∑ T : Clusters S, f T := by
  rw [← Finset.mul_sum, sum_permutations_eq_cluster_sum]
  have hs : (S.card.factorial : k) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero S.card
  have hc : ((Fintype.card α - S.card).factorial : k) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (Fintype.card α - S.card)
  field_simp

/-- Reindex an arbitrary label sum by actual clusters and their exact label
fibres. No invariance of the summand is needed or silently assumed. -/
theorem sum_permutations_eq_sum_clusterFibers {k : Type*} [AddCommMonoid k]
    (S : Finset α) (f : Equiv.Perm α → k) :
    (∑ σ : Equiv.Perm α, f σ) =
      ∑ T : Clusters S, ∑ σ : ClusterFiber S T.val, f σ.val := by
  rw [← Fintype.sum_fiberwise (movedCluster S) f]
  apply Finset.sum_congr rfl
  intro T hT
  exact Fintype.sum_equiv
    (Equiv.subtypeEquivRight (fun σ ↦ movedCluster_eq_iff S σ T)) _ _ (fun _ ↦ rfl)

/-- Internal averaging is exactly the sum over physical subsets and their
remaining label fibres, with the original global vertex factorial. -/
theorem internalAverage_eq_clusterFibers {k : Type*} [Field k] {n : ℕ}
    (S : Finset (Fin n)) (c : UniformBinaryGraphs.BinaryGraph n 3 → k)
    (H : UniformBinaryGraphs.BinaryGraph n 3) :
    BinaryGraphAveraging.internalAverage c H = (n.factorial : k)⁻¹ *
      ∑ T : Clusters S, ∑ σ : ClusterFiber S T.val, c (H.permuteInternal σ.val.symm) := by
  rw [BinaryGraphAveraging.internalAverage_apply]
  convert congrArg ((n.factorial : k)⁻¹ * ·)
      (sum_permutations_eq_sum_clusterFibers S (fun σ ↦ c (H.permuteInternal σ.symm))) using 1
  · rfl
  · congr 2
    funext T
    congr 1
    ext x
    simp
end EnvelopingIsomorphism.Deformation.GraphLabelledClusterCounting
