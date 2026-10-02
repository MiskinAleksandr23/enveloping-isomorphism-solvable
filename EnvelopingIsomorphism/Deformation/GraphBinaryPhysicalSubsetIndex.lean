import EnvelopingIsomorphism.Deformation.GraphBinaryOutgoingClusterSums

/-! The degree-split cluster index is exactly the set of all physical
internal subsets. This includes the empty and full nullary endpoints. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.GraphBinaryPhysicalSubsetIndex
open GraphBinaryClusterSums GraphLabelledClusterCounting GraphAssociatorProfiles
open scoped Classical BigOperators

abbrev Index (N : ℕ) := (a : Fin (N+1)) × Clusters (innerBlock a (N-a))

def subset {N : ℕ} (p : Index N) : Finset (Fin N) :=
  p.2.val.map (finCongr (splitDegree N p.1)).toEmbedding

theorem subset_card {N : ℕ} (p : Index N) : (subset p).card = N-p.1 := by
  simp only [subset,Finset.card_map,p.2.property,innerBlock_card]

theorem subset_injective (N : ℕ) : Function.Injective (subset (N := N)) := by
  rintro ⟨a,T⟩ ⟨b,U⟩ he
  have hc := congrArg Finset.card he
  rw [subset_card,subset_card] at hc
  have hab : a = b := Fin.ext (by have ha := a.isLt; have hb := b.isLt; dsimp only at hc; omega)
  subst b
  have hT : T = U := Subtype.ext (Finset.map_injective _ he)
  subst U
  rfl

theorem subset_surjective (N : ℕ) : Function.Surjective (subset (N := N)) := by
  intro S
  have hc : S.card ≤ N := by simpa only [Fintype.card_fin] using Finset.card_le_univ S
  let a : Fin (N+1) := ⟨N-S.card,by omega⟩
  let T : Clusters (innerBlock a (N-a)) :=
    ⟨S.map (finCongr (splitDegree N a)).symm.toEmbedding,by
      rw [Finset.card_map,innerBlock_card]
      dsimp only [a]
      omega⟩
  refine ⟨⟨a,T⟩,?_⟩
  change (S.map (finCongr (splitDegree N a)).symm.toEmbedding).map
    (finCongr (splitDegree N a)).toEmbedding = S
  rw [Finset.map_map]
  have he : (finCongr (splitDegree N a)).symm.toEmbedding.trans
      (finCongr (splitDegree N a)).toEmbedding = Function.Embedding.refl _ := by
    apply Function.Embedding.ext
    intro v
    change finCongr (splitDegree N a) ((finCongr (splitDegree N a)).symm v) = v
    exact Equiv.apply_symm_apply _ _
  rw [he,Finset.map_refl]

def indexEquiv (N : ℕ) : Index N ≃ Finset (Fin N) :=
  Equiv.ofBijective subset ⟨subset_injective N,subset_surjective N⟩

theorem outerCount_of_subset {N : ℕ} (p : Index N) : p.1.val = N - (subset p).card := by
  rw [subset_card]
  have h := p.1.isLt
  omega

/-- Every summand in the actual unaveraged real-cluster formula is indexed
once by its original physical subset, including both endpoint subsets. -/
theorem sum_degree_clusters_eq_subsets {N : ℕ}
    (f : ∀ a : Fin (N+1), Clusters (innerBlock a (N-a)) → ℝ) :
    (∑ a : Fin (N+1), ∑ T : Clusters (innerBlock a (N-a)), f a T) =
      ∑ S : Finset (Fin N), f ((indexEquiv N).symm S).1 ((indexEquiv N).symm S).2 := by
  calc
    _ = ∑ p : Index N, f p.1 p.2 := (Fintype.sum_sigma (fun p : Index N => f p.1 p.2)).symm
    _ = _ := (Equiv.sum_comp (indexEquiv N).symm (fun p : Index N => f p.1 p.2)).symm

def indexedCoefficient {N : ℕ} (H : UniformBinaryGraphs.BinaryGraph N 3) (r : Fin 2)
    (p : Index N) : ℝ :=
  rawClusterCoefficient r (castVertices (splitDegree N p.1).symm H) p.2

def coefficient {N : ℕ} (H : UniformBinaryGraphs.BinaryGraph N 3) (r : Fin 2)
    (S : Finset (Fin N)) : ℝ := indexedCoefficient H r ((indexEquiv N).symm S)

/-- Literal physical-subset form of the actual associator side. -/
theorem realClusterSum_eq_subsets {N : ℕ} (H : UniformBinaryGraphs.BinaryGraph N 3) :
    MainScalarBoundaryAssembly.realClusterSum H =
      ∑ S : Finset (Fin N), (coefficient H 0 S - coefficient H 1 S) := by
  rw [GraphBinaryOutgoingClusterSums.realClusterSum_eq_unaveraged,
    sum_degree_clusters_eq_subsets]
  rfl

def indexOfCount {a b N : ℕ} (h : a+b = N) (T : Clusters (innerBlock a b)) : Index N :=
  ⟨⟨a,by omega⟩,by
    have hb : N-a = b := by omega
    dsimp only
    rw [hb]
    exact T⟩

theorem subset_indexOfCount {a b N : ℕ} (h : a+b = N) (T : Clusters (innerBlock a b)) :
    subset (indexOfCount h T) = T.val.map (finCongr h).toEmbedding := by
  have hb : b = N-a := by omega
  subst b
  rfl

/-- A coefficient can be evaluated in any correctly counted representation
of its physical subset; the global index chooses no additional labelling. -/
theorem coefficient_eq_of_count {a b N : ℕ} (h : a+b = N)
    (H : UniformBinaryGraphs.BinaryGraph N 3) (r : Fin 2)
    (T : Clusters (innerBlock a b)) (S : Finset (Fin N))
    (hS : T.val.map (finCongr h).toEmbedding = S) :
    coefficient H r S = rawClusterCoefficient r (castVertices h.symm H) T := by
  have hp : (indexEquiv N).symm S = indexOfCount h T := by
    apply (indexEquiv N).injective
    rw [Equiv.apply_symm_apply]
    exact (subset_indexOfCount h T).trans hS |>.symm
  unfold coefficient
  rw [hp]
  have hb : b = N-a := by omega
  subst b
  rfl

end EnvelopingIsomorphism.Deformation.GraphBinaryPhysicalSubsetIndex
