import EnvelopingIsomorphism.Deformation.Kontsevich.PureBoundaryClusterReconstruction
import EnvelopingIsomorphism.Deformation.Kontsevich.InteriorClusterOriginalCoverage

/-! An actual open positional region at a pure external-cluster face. Every
original configuration in it has a proved reconstruction in the actual domain. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich

open Configuration Set Topology

variable {n m : ℕ} {i : Fin n} {l u : Fin (m + 1)} {a b : Fin m}

theorem isOpen_pureBoundarySmallCluster (a : Fin m) (l u : Fin (m + 1)) :
    IsOpen {p : (Fin n ⊕ Fin m) → ℂ | PureBoundaryClusterReconstruction.SmallCluster a l u p} := by
  simp only [PureBoundaryClusterReconstruction.SmallCluster, setOf_forall]
  apply isOpen_iInter_of_finite
  intro j
  apply isOpen_iInter_of_finite
  intro hj
  apply isOpen_iInter_of_finite
  intro k
  apply isOpen_iInter_of_finite
  intro hk
  apply isOpen_lt <;> fun_prop

def pureBoundaryClusterOriginalCoverageRegion (i : Fin n) (m : ℕ) (l u : Fin (m + 1))
    (a : Fin m) : Set (Compactification i m) :=
  {x | x.val.1 ∈ finitePositionEmbedding ''
    {p : (Fin n ⊕ Fin m) → ℂ | PureBoundaryClusterReconstruction.SmallCluster a l u p}}

theorem isOpen_pureBoundaryClusterOriginalCoverageRegion (i : Fin n) (m : ℕ)
    (l u : Fin (m + 1)) (a : Fin m) :
    IsOpen (pureBoundaryClusterOriginalCoverageRegion i m l u a) :=
  (isOpenEmbedding_finitePositionEmbedding.isOpenMap _ (isOpen_pureBoundarySmallCluster a l u)).preimage
    (continuous_fst.comp continuous_subtype_val)

theorem mem_pureBoundaryClusterOriginalCoverageRegion_embedding_iff (c : Normalized i m) :
    compactificationEmbedding i c ∈ pureBoundaryClusterOriginalCoverageRegion i m l u a ↔
      PureBoundaryClusterReconstruction.SmallCluster a l u c.val.vertexPoint := by
  constructor
  · rintro ⟨p, hp, heq⟩
    have h : p = c.val.vertexPoint := isOpenEmbedding_finitePositionEmbedding.injective heq
    rwa [h] at hp
  · intro hp
    exact ⟨c.val.vertexPoint, hp, rfl⟩

def PureBoundaryClusterData.baseVertex (D : PureBoundaryClusterData i m l u a b)
    (v : Fin n ⊕ Fin m) : ℂ := D.doubledBase (Sum.inl v)

theorem pureBoundarySmallCluster_baseVertex (D : PureBoundaryClusterData i m l u a b) :
    PureBoundaryClusterReconstruction.SmallCluster a l u D.baseVertex := by
  intro j hj k hk
  change |(D.boundaryBase j : ℂ).re - (D.boundaryBase a : ℂ).re| <
    |(D.boundaryBase k : ℂ).re - (D.boundaryBase a : ℂ).re|
  rw [Complex.ofReal_re, Complex.ofReal_re, Complex.ofReal_re,
    D.boundaryBase_eq_center a D.left_mem, D.boundaryBase_eq_center j hj, sub_self, abs_zero]
  exact abs_pos.mpr (sub_ne_zero.mpr (fun h => hk ((D.boundaryBase_eq_center_iff k).mp h)))

theorem boundaryPoint_mem_pureBoundaryClusterOriginalCoverageRegion
    (D : PureBoundaryClusterData i m l u a b) :
    D.boundaryPoint ∈ pureBoundaryClusterOriginalCoverageRegion i m l u a := by
  refine ⟨D.baseVertex, pureBoundarySmallCluster_baseVertex D, ?_⟩
  funext v
  simp only [finitePositionEmbedding, PureBoundaryClusterData.baseVertex,
    PureBoundaryClusterData.boundaryPoint, PureBoundaryClusterData.compactInsertion,
    PureBoundaryClusterData.resolvedCoordinates, Complex.ofReal_zero, zero_mul, add_zero]

theorem original_coverage_in_pureBoundaryClusterRegion (hleft : a.val = l.val)
    (hright : b.val + 1 = u.val) (hab : a < b) :
    pureBoundaryClusterOriginalCoverageRegion i m l u a ∩
      Set.range (compactificationEmbedding i : Normalized i m → _) ⊆
        Set.range (PureBoundaryClusterDomain.insertion : PureBoundaryClusterDomain i m l u a b → _) := by
  rintro _ ⟨hx, c, rfl⟩
  have hsmall := (mem_pureBoundaryClusterOriginalCoverageRegion_embedding_iff c).mp hx
  exact ⟨PureBoundaryClusterReconstruction.domain c hleft hright hab hsmall,
    PureBoundaryClusterReconstruction.insertion_domain c hleft hright hab hsmall⟩

end EnvelopingIsomorphism.Deformation.Kontsevich
