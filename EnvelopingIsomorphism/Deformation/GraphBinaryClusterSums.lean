import EnvelopingIsomorphism.Deformation.GraphLabelledClusterCounting
import EnvelopingIsomorphism.Deformation.GraphBinaryGraftFibres
import EnvelopingIsomorphism.Deformation.GraphCanonicalBinaryWeights
import EnvelopingIsomorphism.Deformation.GraphBinaryGraftRelabelling

/-! Exact labelled real-cluster sums for the canonical associator. Each scalar
summand is a product of the actual extracted geometric weights, with all
internal label factorials and the zero-vertex cases retained. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.GraphBinaryClusterSums
open scoped BigOperators Classical
open UniformBinaryGraphs GraphWeightedInsertion BinaryGraphAveraging
open GraphLabelledClusterCounting GraphBinaryGraftFibres GraphCanonicalBinaryWeights
open GraphBinaryGraftRelabelling

/-- The physical internal cluster in the unpermuted graft labelling. -/
def innerBlock (a b : ℕ) : Finset (Fin (a + b)) :=
  Finset.univ.map ⟨Fin.natAdd a, Fin.natAdd_injective b a⟩

@[simp] theorem innerBlock_card (a b : ℕ) : (innerBlock a b).card = b := by
  simp [innerBlock]

theorem card_innerBlock_fiber {a b : ℕ} (T : Clusters (innerBlock a b)) :
    Fintype.card (ClusterFiber (innerBlock a b) T.val) = a.factorial * b.factorial := by
  have h := card_clusterFiber _ _ T.property.symm
  convert h using 1
  · congr 1
    exact Subsingleton.elim _ _
  · simp [Nat.mul_comm]

def innerIndexEquiv (a b : ℕ) : Fin b ≃ (innerBlock a b) :=
  Equiv.ofBijective (fun v ↦ ⟨Fin.natAdd a v, by simp [innerBlock]⟩) (by
    constructor
    · intro v w h
      exact (Fin.natAdd_injective b a) (congrArg Subtype.val h)
    · rintro ⟨v,hv⟩
      obtain ⟨j,hj,he⟩ := Finset.mem_map.mp hv
      exact ⟨j, Subtype.ext he⟩)

def outerIndexEquiv (a b : ℕ) : Fin a ≃ {v : Fin (a+b) // v ∉ innerBlock a b} :=
  Equiv.ofBijective (fun v ↦ ⟨Fin.castAdd b v, by
    intro h
    obtain ⟨j,hj,he⟩ := Finset.mem_map.mp h
    have hh := congrArg Fin.val he
    simp only [Function.Embedding.coeFn_mk, Fin.val_natAdd, Fin.val_castAdd] at hh
    omega⟩) (by
    constructor
    · intro v w h
      exact Fin.castAdd_injective a b (congrArg Subtype.val h)
    · rintro ⟨v,hv⟩
      obtain ⟨j,rfl⟩ := (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a+b)).surjective v
      cases j with
      | inl j => exact ⟨j, rfl⟩
      | inr j => exact (hv (by simp [innerBlock])).elim)

/-- Every permutation preserving the physical graft partition consists of
independent permutations of the outer and inner factor labels. -/
theorem exists_blockPerm_of_preserves {a b : ℕ} (ρ : Equiv.Perm (Fin (a+b)))
    (hρ : ∀ v, ρ v ∈ innerBlock a b ↔ v ∈ innerBlock a b) :
    ∃ σ : Equiv.Perm (Fin a), ∃ τ : Equiv.Perm (Fin b), blockPerm σ τ = ρ := by
  let D := clusterFiberEquiv (innerBlock a b) (innerBlock a b) ⟨ρ,hρ⟩
  let ei := innerIndexEquiv a b
  let eo := outerIndexEquiv a b
  refine ⟨(eo.trans D.2).trans eo.symm, (ei.trans D.1).trans ei.symm, ?_⟩
  apply Equiv.ext
  intro v
  refine Fin.addCases (fun v ↦ ?_) (fun v ↦ ?_) v
  · rw [blockPerm_outer]
    change (eo (eo.symm (D.2 (eo v)))).val = ρ (Fin.castAdd b v)
    rw [Equiv.apply_symm_apply]
    rfl
  · rw [blockPerm_inner]
    change (ei (ei.symm (D.1 (ei v)))).val = ρ (Fin.natAdd a v)
    rw [Equiv.apply_symm_apply]
    rfl

variable {k : Type*} [Field k] {a b : ℕ}

/-- Two labellings of the same physical cluster give the same actual graft
coefficient when its two factor weights are invariant under internal labels. -/
theorem graftProfile_same_cluster (r : Fin 2)
    (w : BinaryGraph a 2 → k) (v : BinaryGraph b 2 → k)
    (hw : ∀ (Γ : BinaryGraph a 2) (σ : Equiv.Perm (Fin a)), w (Γ.permuteInternal σ) = w Γ)
    (hv : ∀ (Δ : BinaryGraph b 2) (τ : Equiv.Perm (Fin b)), v (Δ.permuteInternal τ) = v Δ)
    (H : BinaryGraph (a+b) 3) (T : Clusters (innerBlock a b))
    (σ τ : ClusterFiber (innerBlock a b) T.val) :
    graftProfile r w v (H.permuteInternal σ.val.symm) =
      graftProfile r w v (H.permuteInternal τ.val.symm) := by
  have hp : ∀ x, (τ.val.trans σ.val.symm) x ∈ innerBlock a b ↔ x ∈ innerBlock a b := by
    intro x
    have hs := σ.property (σ.val.symm (τ.val x))
    simp only [Equiv.apply_symm_apply] at hs
    exact hs.symm.trans (τ.property x)
  obtain ⟨p,q,hpq⟩ := exists_blockPerm_of_preserves (τ.val.trans σ.val.symm) hp
  have he : (H.permuteInternal τ.val.symm).permuteInternal (blockPerm p q) =
      H.permuteInternal σ.val.symm := by
    rw [hpq, KontsevichGraph.General.Graph.permuteInternal_trans]
    congr 1
    apply Equiv.ext
    intro x
    simp
  rw [← he, graftProfile_blockPerm r w v hw hv]

/-- The internal average is the actual finite sum over physical clusters and
all their labellings of extracted products, without graph-producing choices. -/
theorem internalAverage_graft_eq_cluster_sum (r : Fin 2)
    (w : BinaryGraph a 2 → k) (v : BinaryGraph b 2 → k)
    (H : BinaryGraph (a + b) 3) :
    internalAverage (graftProfile r w v) H = ((a + b).factorial : k)⁻¹ *
      ∑ T : Clusters (innerBlock a b), ∑ σ : ClusterFiber (innerBlock a b) T.val,
        extractedCoefficient r w v (H.permuteInternal σ.val.symm) := by
  rw [internalAverage_eq_clusterFibers (innerBlock a b)]
  simp only [graftProfile_eq_extractedCoefficient]

/-- Scalar multiplication commutes with the literal internal average. -/
theorem internalAverage_smul (s : k) (c : BinaryGraph a 3 → k) :
    internalAverage (s • c) = s • internalAverage c := by
  funext H
  simp only [internalAverage_apply, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  ring

/-- Both factor MC factorials, the global averaging factorial, and the actual
extracted raw integrals are now visible in one identity. -/
theorem internalAverage_canonical_graft_eq_cluster_sum (r : Fin 2)
    (H : BinaryGraph (a + b) 3) :
    internalAverage (graftProfile r
      (GraphBoundaryProfiles.canonicalBinaryWeight (k := ℝ) a)
      (GraphBoundaryProfiles.canonicalBinaryWeight (k := ℝ) b)) H =
      ((a + b).factorial : ℝ)⁻¹ * (a.factorial : ℝ)⁻¹ * (b.factorial : ℝ)⁻¹ *
        ∑ T : Clusters (innerBlock a b), ∑ σ : ClusterFiber (innerBlock a b) T.val,
          extractedCoefficient r (rawBinaryWeight a) (rawBinaryWeight b)
            (H.permuteInternal σ.val.symm) := by
  rw [canonical_graftProfile, internalAverage_smul, Pi.smul_apply, smul_eq_mul,
    internalAverage_graft_eq_cluster_sum]
  ring

/-- A physical cluster contributes the uniquely extracted product of raw
geometric weights in any one representative labelling. -/
def rawClusterCoefficient (r : Fin 2) (H : BinaryGraph (a+b) 3)
    (T : Clusters (innerBlock a b)) : ℝ :=
  extractedCoefficient r (rawBinaryWeight a) (rawBinaryWeight b)
    (H.permuteInternal (clusterRepresentative (innerBlock a b) T).val.symm)

theorem sum_raw_cluster_fiber (r : Fin 2) (H : BinaryGraph (a+b) 3)
    (T : Clusters (innerBlock a b)) :
    (∑ σ : ClusterFiber (innerBlock a b) T.val,
      extractedCoefficient r (rawBinaryWeight a) (rawBinaryWeight b)
        (H.permuteInternal σ.val.symm)) =
      (a.factorial : ℝ) * (b.factorial : ℝ) * rawClusterCoefficient r H T := by
  calc
    _ = ∑ _σ : ClusterFiber (innerBlock a b) T.val, rawClusterCoefficient r H T := by
      apply Finset.sum_congr rfl
      intro σ hσ
      unfold rawClusterCoefficient
      simp only [← graftProfile_eq_extractedCoefficient]
      exact graftProfile_same_cluster r (rawBinaryWeight a) (rawBinaryWeight b)
        (rawBinaryWeight_permuteInternal a) (rawBinaryWeight_permuteInternal b) H T σ _
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, card_innerBlock_fiber, nsmul_eq_mul, Nat.cast_mul]

/-- The exact normalized scalar boundary sum: all local label factorials
cancel, leaving one genuine extracted weight product per physical subset. -/
theorem internalAverage_canonical_graft_eq_subsets (r : Fin 2)
    (H : BinaryGraph (a+b) 3) :
    internalAverage (graftProfile r
      (GraphBoundaryProfiles.canonicalBinaryWeight (k := ℝ) a)
      (GraphBoundaryProfiles.canonicalBinaryWeight (k := ℝ) b)) H =
      ((a+b).factorial : ℝ)⁻¹ * ∑ T : Clusters (innerBlock a b), rawClusterCoefficient r H T := by
  rw [internalAverage_canonical_graft_eq_cluster_sum]
  simp only [sum_raw_cluster_fiber, ← Finset.mul_sum]
  have ha : (a.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero a
  have hb : (b.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero b
  field_simp

/-- The actual signed outgoing average of the physical real-boundary cluster
sum, with its global `2^N N!` normalization and no leftover fibre factorials. -/
theorem boundaryAverage_canonical_graft_eq_subsets (r : Fin 2)
    (H : BinaryGraph (a+b) 3) :
    boundaryAverage (graftProfile r
      (GraphBoundaryProfiles.canonicalBinaryWeight (k := ℝ) a)
      (GraphBoundaryProfiles.canonicalBinaryWeight (k := ℝ) b)) H =
      ((2 : ℝ)^(a+b))⁻¹ * ((a+b).factorial : ℝ)⁻¹ *
        ∑ τ : Fin (a+b) → Equiv.Perm (Fin 2), outgoingSign (k := ℝ) τ *
          ∑ T : Clusters (innerBlock a b),
            rawClusterCoefficient r (H.permuteOutgoing (fun v ↦ (τ v).symm)) T := by
  rw [boundaryAverage, outgoingAverage_apply]
  simp only [internalAverage_canonical_graft_eq_subsets]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro τ hτ
  apply Finset.sum_congr rfl
  intro T hT
  ring

/-- The genuine finite internal average as a linear map. -/
def internalAverageLinear {k : Type*} [Field k] (n : ℕ) :
    (BinaryGraph n 3 → k) →ₗ[k] (BinaryGraph n 3 → k) where
  toFun := internalAverage
  map_add' c d := by
    funext H
    simp [internalAverage_apply, Finset.sum_add_distrib, mul_add]
  map_smul' s c := by
    funext H
    simp only [internalAverage_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
      RingHom.id_apply]
    apply Finset.sum_congr rfl
    intro σ hσ
    ring

open GraphAssociatorProfiles

theorem internalAverage_castProfile_apply {k : Type*} [Field k] {n N : ℕ}
    (h : n = N) (c : BinaryGraph n 3 → k) (H : BinaryGraph N 3) :
    internalAverage (castProfile h c) H = internalAverage c (castVertices h.symm H) := by
  cases h
  rfl

/-- The full associator has exactly the left-minus-right physical cluster
sum in every degree, with one common global factorial. This includes every
split and both nullary endpoints. -/
theorem internalAverage_canonical_associator_eq_clusters (N : ℕ) (H : BinaryGraph N 3) :
    internalAverage (associatorProfile N (GraphBoundaryProfiles.canonicalBinaryWeight (k := ℝ))) H =
      (N.factorial : ℝ)⁻¹ * ∑ a : Fin (N+1),
        ∑ T : Clusters (innerBlock a (N-a)),
          (rawClusterCoefficient 0 (castVertices (splitDegree N a).symm H) T -
            rawClusterCoefficient 1 (castVertices (splitDegree N a).symm H) T) := by
  change internalAverageLinear N (associatorProfile N _) H = _
  rw [associatorProfile, map_sum]
  simp only [map_sub, Finset.sum_apply, Pi.sub_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  change internalAverage (castProfile _ _) H - internalAverage (castProfile _ _) H = _
  rw [internalAverage_castProfile_apply, internalAverage_castProfile_apply,
    internalAverage_canonical_graft_eq_subsets, internalAverage_canonical_graft_eq_subsets]
  have hfac : (((a : ℕ) + (N-a)).factorial : ℝ) = (N.factorial : ℝ) := by
    rw [splitDegree N a]
  rw [hfac, ← mul_sub, ← Finset.sum_sub_distrib]

/-- The explicit real-boundary side of the scalar relation, now fully
assembled from actual extracted geometric products and all physical subsets.
Only the globally signed face matching remains geometric. -/
theorem boundaryAverage_canonical_associator_eq_clusters (N : ℕ) (H : BinaryGraph N 3) :
    boundaryAverage (associatorProfile N (GraphBoundaryProfiles.canonicalBinaryWeight (k := ℝ))) H =
      ((2 : ℝ)^N)⁻¹ * (N.factorial : ℝ)⁻¹ *
        ∑ τ : Fin N → Equiv.Perm (Fin 2), outgoingSign (k := ℝ) τ *
          ∑ a : Fin (N+1), ∑ T : Clusters (innerBlock a (N-a)),
            (rawClusterCoefficient 0
                (castVertices (splitDegree N a).symm (H.permuteOutgoing (fun v ↦ (τ v).symm))) T -
              rawClusterCoefficient 1
                (castVertices (splitDegree N a).symm (H.permuteOutgoing (fun v ↦ (τ v).symm))) T) := by
  rw [boundaryAverage, outgoingAverage_apply]
  simp only [internalAverage_canonical_associator_eq_clusters, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro τ hτ
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro T hT
  ring

end EnvelopingIsomorphism.Deformation.GraphBinaryClusterSums
