import EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryClusterReconstruction
import EnvelopingIsomorphism.Deformation.Kontsevich.InteriorClusterOriginalCoverage

/-! An explicit open positional neighborhood of a finite real-cluster face.
Every original configuration in this neighborhood is reconstructed in the
actual real-cluster insertion domain. The neighborhood also records the
insertion gap when the collapsing boundary block is empty. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich

open Configuration Set Topology

variable {n m : ℕ} {i a : Fin n} {S : Finset (Fin n)} {l u : Fin (m + 1)}

theorem isOpen_boundarySmallCluster (S : Finset (Fin n)) (a : Fin n) (l u : Fin (m + 1)) :
    IsOpen {p : (Fin n ⊕ Fin m) → ℂ | BoundaryClusterReconstruction.SmallCluster S a l u p} := by
  simp only [BoundaryClusterReconstruction.SmallCluster, setOf_and, setOf_forall]
  refine IsOpen.inter ?_ (IsOpen.inter ?_ (IsOpen.inter ?_ ?_))
  · apply isOpen_iInter_of_finite
    intro j
    apply isOpen_iInter_of_finite
    intro hj
    apply isOpen_lt <;> fun_prop
  · apply isOpen_iInter_of_finite
    intro j
    apply isOpen_iInter_of_finite
    intro hj
    apply isOpen_lt <;> fun_prop
  · apply isOpen_iInter_of_finite
    intro j
    apply isOpen_iInter_of_finite
    intro hj
    apply isOpen_iInter_of_finite
    intro k
    apply isOpen_iInter_of_finite
    intro hk
    apply isOpen_lt <;> fun_prop
  · apply isOpen_iInter_of_finite
    intro j
    apply isOpen_iInter_of_finite
    intro hj
    apply isOpen_iInter_of_finite
    intro k
    apply isOpen_iInter_of_finite
    intro hk
    apply isOpen_lt <;> fun_prop

/-- A neighborhood in the actual compact closure, expressed solely through finite positions. -/
def boundaryClusterOriginalCoverageRegion (i a : Fin n) (m : ℕ) (S : Finset (Fin n))
    (l u : Fin (m + 1)) : Set (Compactification i m) :=
  {x | x.val.1 ∈ finitePositionEmbedding ''
    {p : (Fin n ⊕ Fin m) → ℂ | BoundaryClusterReconstruction.SmallCluster S a l u p}}

theorem isOpen_boundaryClusterOriginalCoverageRegion (i a : Fin n) (m : ℕ)
    (S : Finset (Fin n)) (l u : Fin (m + 1)) :
    IsOpen (boundaryClusterOriginalCoverageRegion i a m S l u) :=
  (isOpenEmbedding_finitePositionEmbedding.isOpenMap _ (isOpen_boundarySmallCluster S a l u)).preimage
    (continuous_fst.comp continuous_subtype_val)

theorem mem_boundaryClusterOriginalCoverageRegion_embedding_iff (c : Normalized i m) :
    compactificationEmbedding i c ∈ boundaryClusterOriginalCoverageRegion i a m S l u ↔
      BoundaryClusterReconstruction.SmallCluster S a l u c.val.vertexPoint := by
  constructor
  · rintro ⟨p, hp, heq⟩
    have h : p = c.val.vertexPoint := isOpenEmbedding_finitePositionEmbedding.injective heq
    rwa [h] at hp
  · intro hp
    exact ⟨c.val.vertexPoint, hp, rfl⟩

theorem boundarySmallCluster_baseVertex (D : BoundaryClusterData i a m S l u) :
    BoundaryClusterReconstruction.SmallCluster S a l u D.baseVertex := by
  have ha := D.base_eq_center a D.anchor_mem
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j hj
    change (D.boundaryBase j : ℂ).re < (D.base a).re
    simpa only [ha, Complex.ofReal_re] using D.boundaryBase_lt_center j hj
  · intro j hj
    change (D.base a).re < (D.boundaryBase j : ℂ).re
    simpa only [ha, Complex.ofReal_re] using D.center_lt_boundaryBase j hj
  · intro j hj k hk
    change ‖D.base j - ((D.base a).re : ℂ)‖ < ‖((D.base a).re : ℂ) - D.base k‖
    rw [ha, Complex.ofReal_re, D.base_eq_center j hj, sub_self, norm_zero]
    exact norm_pos_iff.mpr (sub_ne_zero.mpr
      (fun h => hk ((D.base_eq_center_iff k).mp h.symm)))
  · intro j hj k hk
    change |(D.boundaryBase j : ℂ).re - (D.base a).re| <
      |(D.boundaryBase k : ℂ).re - (D.base a).re|
    rw [ha, Complex.ofReal_re, Complex.ofReal_re, Complex.ofReal_re,
      D.boundaryBase_eq_center j hj, sub_self, abs_zero]
    exact abs_pos.mpr (sub_ne_zero.mpr
      (fun h => hk ((D.boundaryBase_eq_center_iff k).mp h)))

theorem boundaryPoint_mem_boundaryClusterOriginalCoverageRegion (D : BoundaryClusterData i a m S l u) :
    D.boundaryPoint ∈ boundaryClusterOriginalCoverageRegion i a m S l u := by
  refine ⟨D.baseVertex, boundarySmallCluster_baseVertex D, ?_⟩
  funext v
  exact (D.boundaryPoint_position v).symm

/-- Every original configuration in the explicit open region belongs to the actual chart image. -/
theorem original_coverage_in_boundaryClusterRegion (ha : a ∈ S) (hi : i ∉ S) (hcut : l ≤ u) :
    boundaryClusterOriginalCoverageRegion i a m S l u ∩
      Set.range (compactificationEmbedding i : Normalized i m → _) ⊆
        Set.range (BoundaryClusterDomain.insertion : BoundaryClusterDomain i a m S l u → _) := by
  rintro _ ⟨hx, c, rfl⟩
  have hsmall := (mem_boundaryClusterOriginalCoverageRegion_embedding_iff c).mp hx
  exact ⟨BoundaryClusterReconstruction.domain c ha hi hcut hsmall,
    BoundaryClusterReconstruction.insertion_domain c ha hi hcut hsmall⟩

end EnvelopingIsomorphism.Deformation.Kontsevich
