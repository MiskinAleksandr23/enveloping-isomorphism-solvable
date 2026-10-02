import EnvelopingIsomorphism.Deformation.MixedPhysicalBoundaryNormalization
import EnvelopingIsomorphism.Deformation.MixedRealPhysicalIndex

/-! Exact physical binary-subset indexing of the mixed target action. The
full internal subset is absent because the vector factor has a vertex. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.MixedGraphPhysicalSubsetIndex
open MixedGraphClusterSums MixedGraphLabelledClusterCounting MixedGraphTargetProfiles
open MixedGraphProfileCarrier GraphLabelledClusterCounting
open scoped Classical BigOperators

abbrev Index (N : ℕ) := (a : Fin (N+1)) × Clusters (binaryBlock a (N-a))
abbrev NonfullSubset (N : ℕ) := {S : Finset (Fin (N+1)) // S.card ≤ N}

def subset {N : ℕ} (p : Index N) : NonfullSubset N :=
  ⟨p.2.val.map (finCongr (congrArg (· + 1) (splitDegree N p.1))).toEmbedding,by
    rw [Finset.card_map,p.2.property,card_binaryBlock]
    omega⟩

theorem subset_card {N : ℕ} (p : Index N) : (subset p).val.card = N-p.1 := by
  simp only [subset,Finset.card_map,p.2.property,card_binaryBlock]

theorem subset_injective (N : ℕ) : Function.Injective (subset (N := N)) := by
  rintro ⟨a,T⟩ ⟨b,U⟩ he
  have hc := congrArg (fun S : NonfullSubset N => S.val.card) he
  rw [subset_card,subset_card] at hc
  have hab : a = b := Fin.ext (by have ha := a.isLt; have hb := b.isLt; dsimp only at hc; omega)
  subst b
  have hT : T = U := Subtype.ext (Finset.map_injective _ (congrArg Subtype.val he))
  subst U
  rfl

theorem subset_surjective (N : ℕ) : Function.Surjective (subset (N := N)) := by
  intro S
  have hc : S.val.card ≤ N := S.property
  let a : Fin (N+1) := ⟨N-S.val.card,by omega⟩
  let e := finCongr (congrArg (· + 1) (splitDegree N a))
  let T : Clusters (binaryBlock a (N-a)) :=
    ⟨S.val.map e.symm.toEmbedding,by
      rw [Finset.card_map,card_binaryBlock]
      dsimp only [a]
      omega⟩
  refine ⟨⟨a,T⟩,Subtype.ext ?_⟩
  change (S.val.map e.symm.toEmbedding).map e.toEmbedding = S.val
  rw [Finset.map_map]
  have he : e.symm.toEmbedding.trans e.toEmbedding = Function.Embedding.refl _ := by
    apply Function.Embedding.ext
    intro v
    change e (e.symm v) = v
    exact Equiv.apply_symm_apply _ _
  rw [he,Finset.map_refl]

def indexEquiv (N : ℕ) : Index N ≃ NonfullSubset N :=
  Equiv.ofBijective subset ⟨subset_injective N,subset_surjective N⟩

def indexedCoefficient {N : ℕ} (H : VectorGraph N 2) (p : Index N) : ℝ :=
  rawActionClusterCoefficient (castVertices (splitDegree N p.1).symm H) p.2

def coefficient {N : ℕ} (H : VectorGraph N 2) (S : Finset (Fin (N+1))) : ℝ :=
  if hs : S.card ≤ N then indexedCoefficient H ((indexEquiv N).symm ⟨S,hs⟩) else 0

def indexOfCount {a b N : ℕ} (h : a+b = N) (T : Clusters (binaryBlock a b)) : Index N :=
  ⟨⟨a,by omega⟩,by
    have hb : N-a = b := by omega
    dsimp only
    rw [hb]
    exact T⟩

theorem subset_indexOfCount {a b N : ℕ} (h : a+b = N) (T : Clusters (binaryBlock a b)) :
    (subset (indexOfCount h T)).val = T.val.map (finCongr (congrArg (· + 1) h)).toEmbedding := by
  have hb : b = N-a := by omega
  subst b
  rfl

theorem coefficient_eq_of_count {a b N : ℕ} (h : a+b = N)
    (H : VectorGraph N 2) (T : Clusters (binaryBlock a b)) (S : Finset (Fin (N+1)))
    (hS : T.val.map (finCongr (congrArg (· + 1) h)).toEmbedding = S) :
    coefficient H S = rawActionClusterCoefficient (castVertices h.symm H) T := by
  have hc : S.card ≤ N := by
    rw [← hS,Finset.card_map,T.property,card_binaryBlock]
    omega
  have hp : (indexEquiv N).symm ⟨S,hc⟩ = indexOfCount h T := by
    apply (indexEquiv N).injective
    rw [Equiv.apply_symm_apply]
    apply Subtype.ext
    exact ((subset_indexOfCount h T).trans hS).symm
  rw [coefficient,dif_pos hc,hp]
  have hb : b = N-a := by omega
  subst b
  rfl

theorem coefficient_subset {N : ℕ} (H : VectorGraph N 2) (p : Index N) :
    coefficient H (subset p).val = indexedCoefficient H p := by
  rw [coefficient,dif_pos (subset p).property]
  exact congrArg (indexedCoefficient H) ((indexEquiv N).symm_apply_apply p)

theorem targetSum_eq_subsets {N : ℕ} (H : VectorGraph N 2) :
    MixedPhysicalBoundaryNormalization.targetSum H = ∑ S : Finset (Fin (N+1)), coefficient H S := by
  change (∑ a : Fin (N+1), ∑ T : Clusters (binaryBlock a (N-a)), indexedCoefficient H ⟨a,T⟩) = _
  rw [← Fintype.sum_sigma]
  apply Fintype.sum_of_injective (fun p : Index N => (subset p).val)
    (fun p q he => subset_injective N (Subtype.ext he))
  · intro S hS
    apply dif_neg
    intro hc
    obtain ⟨p,hp⟩ := subset_surjective N ⟨S,hc⟩
    exact hS ⟨p,congrArg Subtype.val hp⟩
  · intro p
    exact (coefficient_subset H p).symm

theorem castVertices_vertex_map {a b N : ℕ} (h : a+b = N) (H : VectorGraph N 2) :
    finCongr (congrArg (· + 1) h) (castVertices h.symm H).vertex = H.vertex := by
  subst N
  rfl

/-- A binary cluster cannot contain the distinguished vector. Its actual
finite output and input graft fibres are empty, so the coefficient is zero. -/
theorem coefficient_eq_zero_of_vector_mem {N : ℕ} (H : VectorGraph N 2)
    (S : Finset (Fin (N+1))) (hv : H.vertex ∈ S) : coefficient H S = 0 := by
  unfold coefficient
  split_ifs with hc
  · let p := (indexEquiv N).symm ⟨S,hc⟩
    have hp : (subset p).val = S := congrArg Subtype.val ((indexEquiv N).apply_symm_apply ⟨S,hc⟩)
    change indexedCoefficient H p = 0
    apply rawActionClusterCoefficient_eq_zero_of_vector_mem
    rw [← hp] at hv
    obtain ⟨w,hw,he⟩ := Finset.mem_map.mp hv
    have heq : w = (castVertices (splitDegree N p.1).symm H).vertex :=
      (finCongr (congrArg (· + 1) (splitDegree N p.1))).injective
        (he.trans (castVertices_vertex_map (splitDegree N p.1) H).symm)
    rwa [heq] at hw
  · rfl

/-- Every nonzero mixed target term is either the empty binary subset or a
nonempty subset omitting the distinguished vector. The empty subset carries
both the pure output and the two full-cluster infinity input endpoints. -/
theorem targetSum_eq_empty_add_binarySubsets {N : ℕ} (H : VectorGraph N 2) :
    MixedPhysicalBoundaryNormalization.targetSum H = coefficient H ∅ +
      ∑ T : MixedRealPhysicalIndex.BinarySubset H.vertex, coefficient H T.val := by
  rw [targetSum_eq_subsets]
  have hs : (∑ T : MixedRealPhysicalIndex.BinarySubset H.vertex, coefficient H T.val) =
      ∑ S : Finset (Fin (N+1)), if S.Nonempty ∧ H.vertex ∉ S then coefficient H S else 0 := by
    apply Fintype.sum_of_injective Subtype.val Subtype.val_injective
    · intro S hS
      apply if_neg
      intro hp
      exact hS ⟨⟨S,hp⟩,rfl⟩
    · intro T
      exact (if_pos T.property).symm
  have hp (S : Finset (Fin (N+1))) : coefficient H S =
      (if S = ∅ then coefficient H ∅ else 0) +
        (if S.Nonempty ∧ H.vertex ∉ S then coefficient H S else 0) := by
    by_cases h0 : S = ∅
    · subst S
      simp
    · have hn := Finset.nonempty_iff_ne_empty.mpr h0
      by_cases hv : H.vertex ∈ S
      · rw [coefficient_eq_zero_of_vector_mem H S hv]
        simp [h0,hv]
      · simp [h0,hn,hv]
  calc
    _ = ∑ S : Finset (Fin (N+1)),
        ((if S = ∅ then coefficient H ∅ else 0) +
          (if S.Nonempty ∧ H.vertex ∉ S then coefficient H S else 0)) :=
      Finset.sum_congr rfl (fun S _ => hp S)
    _ = _ := by
      simp only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
      rw [← hs]

end EnvelopingIsomorphism.Deformation.MixedGraphPhysicalSubsetIndex
