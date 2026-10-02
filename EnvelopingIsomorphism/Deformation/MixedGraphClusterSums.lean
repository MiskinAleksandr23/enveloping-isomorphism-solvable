import EnvelopingIsomorphism.Deformation.MixedGraphBlockRelabelling
import EnvelopingIsomorphism.Deformation.MixedGraphCanonicalRelabelling
import EnvelopingIsomorphism.Deformation.MixedGraphLabelledClusterCounting
import EnvelopingIsomorphism.Deformation.GraphBinaryClusterSums

/-! Actual mixed target coefficients indexed by physical binary clusters.
The dependent vector arity, incoming choices, and both factorials are retained
until their proven relabelling fibres are cancelled. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
namespace EnvelopingIsomorphism.Deformation.MixedGraphClusterSums
open scoped BigOperators Classical
open KontsevichGraph.General
open MixedGraphProfileCarrier MixedGraphTargetProfiles MixedGraphAveraging
open MixedGraphBlockRelabelling MixedGraphLabelledClusterCounting
open GraphLabelledClusterCounting UniformBinaryGraphs
variable {a b n : ℕ}

theorem binaryBlock_eq_map (a b : ℕ) :
    binaryBlock a b = (GraphBinaryClusterSums.innerBlock (a + 1) b).map
      (outputVertexEquiv a b).toEmbedding := by
  simp only [binaryBlock, GraphBinaryClusterSums.innerBlock, Finset.map_map]
  rfl

@[simp] theorem outputVertexEquiv_mem_binaryBlock (v : Fin ((a + 1) + b)) :
    outputVertexEquiv a b v ∈ binaryBlock a b ↔
      v ∈ GraphBinaryClusterSums.innerBlock (a + 1) b := by
  rw [binaryBlock_eq_map]
  simp

/-- Every relabelling preserving the physical mixed binary block has the
actual independent vector-factor and binary-factor permutations. -/
theorem exists_blockPerm_of_preserves (ρ : Equiv.Perm (Fin ((a + b) + 1)))
    (hρ : ∀ v, ρ v ∈ binaryBlock a b ↔ v ∈ binaryBlock a b) :
    ∃ σ : Equiv.Perm (Fin (a + 1)), ∃ τ : Equiv.Perm (Fin b), blockPerm σ τ = ρ := by
  let e := outputVertexEquiv a b
  let η := e.trans (ρ.trans e.symm)
  have hp : ∀ v, η v ∈ GraphBinaryClusterSums.innerBlock (a + 1) b ↔
      v ∈ GraphBinaryClusterSums.innerBlock (a + 1) b := by
    intro v
    rw [← outputVertexEquiv_mem_binaryBlock, ← outputVertexEquiv_mem_binaryBlock]
    simpa only [η, e, Equiv.trans_apply, Equiv.apply_symm_apply] using hρ (e v)
  obtain ⟨σ,τ,he⟩ := GraphBinaryClusterSums.exists_blockPerm_of_preserves η hp
  refine ⟨σ,τ,?_⟩
  apply Equiv.ext
  intro v
  have hh := congrArg (fun f => e (f (e.symm v))) he
  change e (SlotRelabelling.blockVertices σ τ (e.symm v)) = _ at hh
  change e (SlotRelabelling.blockVertices σ τ (e.symm v)) = ρ v
  simpa only [η, Equiv.trans_apply, Equiv.apply_symm_apply] using hh

variable {k : Type*} [Field k]

/-- All labels of the same physical cluster give the same genuine mixed
coefficient, proved by the actual dependent block covariance. -/
theorem actionProfile_same_cluster (w : VectorGraph a 1 → k) (v : BinaryGraph b 2 → k)
    (hw : ∀ Γ σ, w (internalGraphEquiv σ 1 Γ) = w Γ)
    (hv : ∀ Δ τ, v (Δ.permuteInternal τ) = v Δ)
    (H : VectorGraph (a + b) 2) (T : Clusters (binaryBlock a b))
    (σ τ : ClusterFiber (binaryBlock a b) T.val) :
    actionProfile w v ((internalGraphEquiv σ.val 2).symm H) =
      actionProfile w v ((internalGraphEquiv τ.val 2).symm H) := by
  have hp : ∀ x, (τ.val.trans σ.val.symm) x ∈ binaryBlock a b ↔ x ∈ binaryBlock a b := by
    intro x
    have hs := σ.property (σ.val.symm (τ.val x))
    simp only [Equiv.apply_symm_apply] at hs
    exact hs.symm.trans (τ.property x)
  obtain ⟨p,q,hpq⟩ := exists_blockPerm_of_preserves (τ.val.trans σ.val.symm) hp
  simp only [internalGraphEquiv_symm_apply]
  have he : internalGraphEquiv (blockPerm p q) 2 (internalGraphEquiv τ.val.symm 2 H) =
      internalGraphEquiv σ.val.symm 2 H := by
    have heperm : τ.val.symm.trans (τ.val.trans σ.val.symm) = σ.val.symm := by
      apply Equiv.ext
      intro x
      simp
    rw [hpq, internalGraphEquiv_trans, heperm]
  rw [← he, actionProfile_blockPerm w v hw hv]

theorem card_binaryBlock_fiber (T : Clusters (binaryBlock a b)) :
    Fintype.card (ClusterFiber (binaryBlock a b) T.val) = (a + 1).factorial * b.factorial := by
  have h := card_clusterFiber (binaryBlock a b) T.val T.property.symm
  convert h using 1
  · congr 1
    exact Subsingleton.elim _ _
  · have hn : (a + b + 1) - b = a + 1 := by omega
    simp [hn, Nat.mul_comm]

/-- The global average uses N+1 actual internal vertices, including the vector. -/
def internalAverageLinear (n : ℕ) : (VectorGraph n 2 → k) →ₗ[k] (VectorGraph n 2 → k) where
  toFun := internalAverage
  map_add' c d := by
    funext H
    simp [internalAverage_apply, Finset.sum_add_distrib, mul_add]
  map_smul' s c := by
    funext H
    simp only [internalAverage_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]
    apply Finset.sum_congr rfl
    intro σ _
    ring


theorem outputProfile_smul_weights (s t : k) (w : VectorGraph a 1 → k) (v : BinaryGraph b 2 → k) :
    outputProfile (s • w) (t • v) = (s * t) • outputProfile w v := by
  funext H
  simp only [outputProfile, GraphCoefficientProfiles.pushforward, Pi.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro D _
  split_ifs <;> ring

theorem inputProfile_smul_weights (r : Fin 2) (s t : k)
    (w : VectorGraph a 1 → k) (v : BinaryGraph b 2 → k) :
    inputProfile r (s • w) (t • v) = (s * t) • inputProfile r w v := by
  funext H
  simp only [inputProfile, GraphCoefficientProfiles.pushforward, Pi.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro D _
  split_ifs <;> ring

theorem actionProfile_smul_weights (s t : k) (w : VectorGraph a 1 → k) (v : BinaryGraph b 2 → k) :
    actionProfile (s • w) (t • v) = (s * t) • actionProfile w v := by
  simp only [actionProfile, outputProfile_smul_weights, inputProfile_smul_weights, smul_sub]

theorem internalAverage_smul (s : k) (c : VectorGraph n 2 → k) :
    internalAverage (s • c) = s • internalAverage c :=
  (internalAverageLinear n).map_smul s c

/-- Raw velocity integral, removing only its internal (n+1)! MC factorial. -/
def rawVelocityWeight (n : ℕ) (Γ : VectorGraph n 1) : ℝ :=
  Kontsevich.GeometricWeights.canonicalWeight Γ.graph
    (Gauge.PlacedMixedGraphTaylorCoefficients.edgeCount 1 Γ.vertex)

theorem canonicalVelocityWeight_eq_factorial (Γ : VectorGraph n 1) :
    MixedGraphBoundaryProfiles.canonicalVelocityWeight (k := ℝ) Γ =
      ((n + 1).factorial : ℝ)⁻¹ * rawVelocityWeight n Γ := by
  simp only [MixedGraphBoundaryProfiles.canonicalVelocityWeight, rawVelocityWeight,
    Kontsevich.GeometricWeights.canonicalEffectiveWeight]
  simp [Kontsevich.effectiveMCWeight, Rat.smul_def]

theorem rawVelocityWeight_internalGraphEquiv (n : ℕ) (Γ : VectorGraph n 1)
    (σ : Equiv.Perm (Fin (n + 1))) :
    rawVelocityWeight n (internalGraphEquiv σ 1 Γ) = rawVelocityWeight n Γ :=
  Kontsevich.GeometricWeights.canonicalWeight_oneExceptionalGraphEquiv 1 Γ.vertex σ Γ.graph _ _

open GraphCanonicalBinaryWeights

theorem canonical_actionProfile :
    actionProfile (MixedGraphBoundaryProfiles.canonicalVelocityWeight (k := ℝ) (n := a))
      (GraphBoundaryProfiles.canonicalBinaryWeight (k := ℝ) b) =
      (((a + 1).factorial : ℝ)⁻¹ * (b.factorial : ℝ)⁻¹) •
        actionProfile (rawVelocityWeight a) (rawBinaryWeight b) := by
  have hv : MixedGraphBoundaryProfiles.canonicalVelocityWeight (k := ℝ) (n := a) =
      ((a + 1).factorial : ℝ)⁻¹ • rawVelocityWeight a := by
    funext Γ
    exact canonicalVelocityWeight_eq_factorial Γ
  have hb : GraphBoundaryProfiles.canonicalBinaryWeight (k := ℝ) b =
      (b.factorial : ℝ)⁻¹ • rawBinaryWeight b := by
    funext Γ
    exact canonicalBinaryWeight_eq_factorial b Γ
  rw [hv, hb, actionProfile_smul_weights]

/-- A physical binary cluster has one genuine mixed target coefficient,
independent of the representative's internal labels. -/
def rawActionClusterCoefficient (H : VectorGraph (a + b) 2)
    (T : Clusters (binaryBlock a b)) : ℝ :=
  actionProfile (rawVelocityWeight a) (rawBinaryWeight b)
    ((internalGraphEquiv (clusterRepresentative (binaryBlock a b) T).val 2).symm H)

theorem sum_raw_action_cluster_fiber (H : VectorGraph (a + b) 2)
    (T : Clusters (binaryBlock a b)) :
    (∑ σ : ClusterFiber (binaryBlock a b) T.val,
      actionProfile (rawVelocityWeight a) (rawBinaryWeight b)
        ((internalGraphEquiv σ.val 2).symm H)) =
      ((a + 1).factorial : ℝ) * (b.factorial : ℝ) * rawActionClusterCoefficient H T := by
  calc
    _ = ∑ _σ : ClusterFiber (binaryBlock a b) T.val, rawActionClusterCoefficient H T := by
      apply Finset.sum_congr rfl
      intro σ _
      exact actionProfile_same_cluster (rawVelocityWeight a) (rawBinaryWeight b)
        (rawVelocityWeight_internalGraphEquiv a) (rawBinaryWeight_permuteInternal b) H T σ _
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, card_binaryBlock_fiber, nsmul_eq_mul, Nat.cast_mul]

theorem rawActionClusterCoefficient_eq_zero_of_vector_mem (H : VectorGraph (a + b) 2)
    (T : Clusters (binaryBlock a b)) (h : H.vertex ∈ T.val) : rawActionClusterCoefficient H T = 0 := by
  apply actionProfile_relabel_eq_zero_of_vector_mem
  have he := (movedCluster_eq_iff (binaryBlock a b)
    (clusterRepresentative (binaryBlock a b) T).val T).mpr
      (clusterRepresentative (binaryBlock a b) T).property
  rwa [he]

/-- Both actual factor factorials cancel against their proven label fibre,
leaving the single global (a+b+1)! averaging factor and one term per subset. -/
theorem internalAverage_canonical_action_eq_subsets (H : VectorGraph (a + b) 2) :
    internalAverage (actionProfile
      (MixedGraphBoundaryProfiles.canonicalVelocityWeight (k := ℝ) (n := a))
      (GraphBoundaryProfiles.canonicalBinaryWeight (k := ℝ) b)) H =
      ((a + b + 1).factorial : ℝ)⁻¹ *
        ∑ T : Clusters (binaryBlock a b), rawActionClusterCoefficient H T := by
  rw [canonical_actionProfile, internalAverage_smul, Pi.smul_apply, smul_eq_mul,
    MixedGraphLabelledClusterCounting.internalAverage_eq_clusterFibers (binaryBlock a b)]
  simp only [sum_raw_action_cluster_fiber, ← Finset.mul_sum]
  have ha : ((a + 1).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (a + 1)
  have hb : (b.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero b
  field_simp

theorem internalAverage_castProfile_apply {N : ℕ} (h : n = N)
    (c : VectorGraph n 2 → k) (H : VectorGraph N 2) :
    internalAverage (castProfile h c) H = internalAverage c (castVertices h.symm H) := by
  cases h
  rfl

/-- Full canonical mixed target action as an actual physical-cluster sum.
Every velocity degree and both nullary endpoints remain present. -/
theorem internalAverage_canonical_targetAction_eq_clusters (N : ℕ) (H : VectorGraph N 2) :
    internalAverage (targetActionProfile N
      (fun _ => MixedGraphBoundaryProfiles.canonicalVelocityWeight (k := ℝ))
      (GraphBoundaryProfiles.canonicalBinaryWeight (k := ℝ))) H =
      ((N + 1).factorial : ℝ)⁻¹ * ∑ a : Fin (N + 1),
        ∑ T : Clusters (binaryBlock a (N - a)),
          rawActionClusterCoefficient (castVertices (splitDegree N a).symm H) T := by
  change internalAverageLinear N (targetActionProfile N _ _) H = _
  rw [targetActionProfile, map_sum]
  simp only [Finset.sum_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  change internalAverage (castProfile _ _) H = _
  rw [internalAverage_castProfile_apply, internalAverage_canonical_action_eq_subsets]
  have he : (a : ℕ) + (N - a) + 1 = N + 1 := by rw [splitDegree N a]
  have hf : (((a : ℕ) + (N - a) + 1).factorial : ℝ) = ((N + 1).factorial : ℝ) :=
    congrArg (fun j : ℕ => (j.factorial : ℝ)) he
  rw [hf]

/-- The full outgoing-signed mixed target boundary table, with its exact
2^N (N+1)! global normalization and no leftover label factorials. -/
theorem boundaryAverage_canonical_targetAction_eq_clusters (N : ℕ) (H : VectorGraph N 2) :
    boundaryAverage (targetActionProfile N
      (fun _ => MixedGraphBoundaryProfiles.canonicalVelocityWeight (k := ℝ))
      (GraphBoundaryProfiles.canonicalBinaryWeight (k := ℝ))) H =
      ((2 : ℝ)^N)⁻¹ * ((N + 1).factorial : ℝ)⁻¹ *
        ∑ τ : OutgoingGroup N, outgoingSign (k := ℝ) τ *
          ∑ a : Fin (N + 1), ∑ T : Clusters (binaryBlock a (N - a)),
            rawActionClusterCoefficient
              (castVertices (splitDegree N a).symm ((outgoingGraphEquiv τ 2).symm H)) T := by
  rw [boundaryAverage, outgoingAverage_apply]
  simp only [internalAverage_canonical_targetAction_eq_clusters, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro τ _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro T _
  ring

end EnvelopingIsomorphism.Deformation.MixedGraphClusterSums
