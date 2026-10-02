import EnvelopingIsomorphism.Deformation.Kontsevich.InteriorClusterReconstruction

/-!
# A proved open positional neighborhood covered on original configurations

The neighborhood requires finite positions and strict small-cluster separation
inequalities. It contains the entire normalized simple-cluster face. Every
original configuration in this neighborhood is explicitly reconstructed in the
normalized single-cluster slice.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich

open Configuration ClusterReconstruction Set Topology

variable {n m : ℕ} {i : Fin n} {S : Finset (Fin n)} {a b : Fin n}

theorem isOpen_smallCluster (S : Finset (Fin n)) (a : Fin n) :
    IsOpen {p : (Fin n ⊕ Fin m) → ℂ | SmallCluster S a p} := by
  change IsOpen ({p : (Fin n ⊕ Fin m) → ℂ |
    ∀ j ∈ S, ‖p (Sum.inl j) - p (Sum.inl a)‖ < (p (Sum.inl a)).im} ∩
    {p | ∀ j ∈ S, ∀ k, k ∉ S → ‖p (Sum.inl j) - p (Sum.inl a)‖ < ‖p (Sum.inl a) - p (Sum.inl k)‖})
  apply IsOpen.inter
  · have heq : {p : (Fin n ⊕ Fin m) → ℂ |
        ∀ j ∈ S, ‖p (Sum.inl j) - p (Sum.inl a)‖ < (p (Sum.inl a)).im} =
        ⋂ (j : Fin n) (_ : j ∈ S),
          {p | ‖p (Sum.inl j) - p (Sum.inl a)‖ < (p (Sum.inl a)).im} := by ext p; simp
    rw [heq]
    apply isOpen_iInter_of_finite
    intro j
    apply isOpen_iInter_of_finite
    intro hj
    exact isOpen_lt ((continuous_apply (Sum.inl j)).sub (continuous_apply (Sum.inl a))).norm
      (Complex.continuous_im.comp (continuous_apply (Sum.inl a)))
  · have heq : {p : (Fin n ⊕ Fin m) → ℂ |
        ∀ j ∈ S, ∀ k, k ∉ S → ‖p (Sum.inl j) - p (Sum.inl a)‖ < ‖p (Sum.inl a) - p (Sum.inl k)‖} =
        ⋂ (j : Fin n) (_ : j ∈ S) (k : Fin n) (_ : k ∉ S),
          {p | ‖p (Sum.inl j) - p (Sum.inl a)‖ < ‖p (Sum.inl a) - p (Sum.inl k)‖} := by ext p; simp
    rw [heq]
    apply isOpen_iInter_of_finite
    intro j
    apply isOpen_iInter_of_finite
    intro hj
    apply isOpen_iInter_of_finite
    intro k
    apply isOpen_iInter_of_finite
    intro hk
    exact isOpen_lt ((continuous_apply (Sum.inl j)).sub (continuous_apply (Sum.inl a))).norm
      ((continuous_apply (Sum.inl a)).sub (continuous_apply (Sum.inl k))).norm

def finitePositionEmbedding : ((Fin n ⊕ Fin m) → ℂ) → ((Fin n ⊕ Fin m) → OnePoint ℂ) :=
  fun p v => (p v : OnePoint ℂ)

theorem isOpenEmbedding_finitePositionEmbedding :
    IsOpenEmbedding (finitePositionEmbedding : ((Fin n ⊕ Fin m) → ℂ) → _) :=
  IsOpenEmbedding.piMap (fun _ : Fin n ⊕ Fin m => OnePoint.isOpenEmbedding_coe)

/-- The open ambient neighborhood defined entirely by finite position coordinates. -/
def clusterOriginalCoverageRegion (i : Fin n) (m : ℕ) (S : Finset (Fin n)) (a : Fin n) :
    Set (Compactification i m) :=
  {x | x.val.1 ∈ finitePositionEmbedding '' {p : (Fin n ⊕ Fin m) → ℂ | SmallCluster S a p}}

theorem isOpen_clusterOriginalCoverageRegion (i : Fin n) (m : ℕ) (S : Finset (Fin n)) (a : Fin n) :
    IsOpen (clusterOriginalCoverageRegion i m S a) :=
  (isOpenEmbedding_finitePositionEmbedding.isOpenMap _ (isOpen_smallCluster S a)).preimage
    (continuous_fst.comp continuous_subtype_val)

theorem mem_clusterOriginalCoverageRegion_embedding_iff (c : Normalized i m) :
    compactificationEmbedding i c ∈ clusterOriginalCoverageRegion i m S a ↔
      SmallCluster S a c.val.vertexPoint := by
  constructor
  · rintro ⟨p, hp, heq⟩
    have h : p = c.val.vertexPoint := isOpenEmbedding_finitePositionEmbedding.injective heq
    rwa [h] at hp
  · intro hp
    exact ⟨c.val.vertexPoint, hp, rfl⟩

theorem smallCluster_baseVertex (D : SingleInteriorCluster i m S) (ha : a ∈ S) :
    SmallCluster S a D.toInteriorCollisionData.baseVertex := by
  constructor
  · intro j hj
    change ‖(D.base j : ℂ) - (D.base a : ℂ)‖ < (D.base a).im
    rw [D.base_eq_of_mem hj ha, sub_self, norm_zero]
    exact (D.base a).im_pos
  · intro j hj k hk
    change ‖(D.base j : ℂ) - (D.base a : ℂ)‖ < ‖(D.base a : ℂ) - (D.base k : ℂ)‖
    rw [D.base_eq_of_mem hj ha, sub_self, norm_zero]
    apply norm_pos_iff.mpr
    apply sub_ne_zero.mpr
    intro heq
    rcases (D.base_eq_iff a k).mp (UpperHalfPlane.ext heq) with hak | hs
    · exact hk (hak ▸ ha)
    · exact hk hs.2

theorem boundaryPoint_mem_clusterOriginalCoverageRegion (D : SingleInteriorCluster i m S) (ha : a ∈ S) :
    D.toInteriorCollisionData.boundaryPoint ∈ clusterOriginalCoverageRegion i m S a := by
  refine ⟨D.toInteriorCollisionData.baseVertex, smallCluster_baseVertex D ha, ?_⟩
  funext v
  exact (D.toInteriorCollisionData.boundaryPoint_position v).symm

/-- Every original configuration in the open positional neighborhood is in the actual slice image. -/
theorem original_coverage_in_clusterRegion (ha : a ∈ S) (hb : b ∈ S) (hba : b ≠ a)
    (hanchor : i ∈ S → a = i) :
    clusterOriginalCoverageRegion i m S a ∩ Set.range (compactificationEmbedding i : Normalized i m → _) ⊆
      Set.range (NormalizedInteriorClusterSlice.insertion : NormalizedInteriorClusterSlice i m S a b → _) := by
  rintro _ ⟨hx, c, rfl⟩
  have hsmall := (mem_clusterOriginalCoverageRegion_embedding_iff c).mp hx
  exact ⟨ClusterReconstruction.slice c ha hb hba hanchor hsmall,
    ClusterReconstruction.insertion_slice c ha hb hba hanchor hsmall⟩

end EnvelopingIsomorphism.Deformation.Kontsevich
