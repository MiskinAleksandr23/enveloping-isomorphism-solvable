import EnvelopingIsomorphism.Deformation.Kontsevich.RealForestBinaryRowSign
import EnvelopingIsomorphism.Deformation.GraphBinaryClusterNativeMatching

/-! Matching the true anchored binary real-face graft with its physical
cluster coefficient, retaining both boundary casts and actual graph data. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace EnvelopingIsomorphism.Deformation.Kontsevich.MainRealGraftPhysicalCoefficient
open scoped Classical BigOperators
open KontsevichGraph.General UniformBinaryGraphs GraphCanonicalBinaryWeights
open GraphBinaryClusterSums GraphLabelledClusterCounting GraphBinaryGraftFibres
open BoundaryGraphFaceFactorization BoundaryGraphOrderedCoordinates BoundaryGraphGraftReconstruction
open BoundaryGraphValenceSelection BoundaryGraphExtractedOrders BoundaryGraphCanonicalFibreMatching

theorem reindex_refl {n m : ℕ} {q : Fin n → ℕ} (G : Graph q m) :
    G.reindex (Equiv.refl _) (Equiv.refl _) = G := by
  apply Graph.ext
  funext ⟨v,j⟩
  simp [Graph.reindex_target]
  rfl

theorem canonicalWeight_eq_raw_cast {N M : ℕ} (hM : M = 2)
    (G : Graph (fun _ : Fin (N+1) ↦ 2) M)
    (hD : ∑ _ : Fin (N+1), 2 = GraphForms.dimension N M) :
    GeometricWeights.canonicalWeight G hD =
      rawBinaryWeight (N+1) (G.reindex (Equiv.refl _) (finCongr hM.symm)) := by
  subst M
  rw [show finCongr (Eq.refl 2).symm = Equiv.refl (Fin 2) from rfl, reindex_refl]
  rfl

theorem canonicalWeight_inner_eq_raw_cast {N M : ℕ} (hM : M = 2)
    (G : Graph (fun _ : Fin (N+1) ↦ 2) (M-1+1))
    (hD : ∑ _ : Fin (N+1), 2 = GraphForms.dimension N M)
    (hpos : M-1+1 = M) :
    GeometricWeights.canonicalWeight (G.reindex (Equiv.refl _) (finCongr hpos.symm)) hD =
      rawBinaryWeight (N+1) (G.reindex (Equiv.refl _) (finCongr (show 2 = M-1+1 by omega))) := by
  subst M
  rw [show finCongr hpos.symm = Equiv.refl (Fin 2) from rfl, reindex_refl]
  rfl

/-- Transport the actual native graft through the ordered boundary-count
casts, using the proved geometric coefficient identities below. -/
theorem graftProfile_reindex_binary {A B O I N : ℕ}
    (hO : O = 1) (hI : I = 1) (r : Fin (O+1))
    (w : BinaryGraph A (O+1) → ℝ) (v : BinaryGraph B (I+1) → ℝ)
    (hw : ∀ G, w G = rawBinaryWeight A
      (G.reindex (Equiv.refl _) (finCongr (show 2 = O+1 by omega))))
    (hv : ∀ G, v G = rawBinaryWeight B
      (G.reindex (Equiv.refl _) (finCongr (show 2 = I+1 by omega))))
    (H : BinaryGraph N 3) (e : Fin (A+B) ≃ Fin N)
    (eB : Fin (O+I+1) ≃ Fin 3) (heB : ∀ j, (eB j).val = j.val) :
    GraphGeneralWeightedGraft.graftProfile r w v (H.reindexForGraft e eB) =
      GraphGeneralWeightedGraft.graftProfile (Fin.cast (show O+1 = 2 by omega) r)
        (rawBinaryWeight A) (rawBinaryWeight B)
        (H.reindexForGraft (o := 1) (l := 1) e (Equiv.refl _)) := by
  subst O
  subst I
  have heB' : eB = Equiv.refl _ := by ext j; exact heB j
  subst eB
  have hw' : w = rawBinaryWeight A := by
    funext G
    simpa only [show finCongr (Eq.refl 2) = Equiv.refl (Fin 2) from rfl, reindex_refl] using hw G
  have hv' : v = rawBinaryWeight B := by
    funext G
    simpa only [show finCongr (Eq.refl 2) = Equiv.refl (Fin 2) from rfl, reindex_refl] using hv G
  rw [hw', hv']
  rfl

section Actual
variable {n : ℕ} {i a : Fin n} {S : Finset (Fin n)} {l u : Fin 4}

theorem outsideM_eq_one (hsize : shapeM l u = 2) : outsideM l u = 1 := by
  have h := boundary_card_sum (l := l) (u := u)
  omega

def physicalSlot (hlt : l < u) (hsize : shapeM l u = 2) : Fin 2 :=
  Fin.cast (congrArg (fun j ↦ j+1) (outsideM_eq_one hsize)) (centerSlot hlt.le)

@[simp] theorem physicalSlot_val (hlt : l < u) (hsize : shapeM l u = 2) :
    (physicalSlot hlt hsize).val = l.val := rfl

variable (H : BinaryGraph n 3) (ha : a ∈ S) (hi : i ∉ S)
    (order : Fin (shapeDegree a S l u + coarseDegree i S l u) ≃ KontsevichGraph.General.Edge (fun _ : Fin n ↦ 2))
    (hc : Fintype.card {j // (graphEdges H order j).1 ∈ S} = shapeDegree a S l u)

theorem canonical_graft_eq_raw_native (hlt : l < u) (hsize : shapeM l u = 2) :
    GraphGeneralWeightedGraft.graftProfile (centerSlot hlt.le)
      (outerCoefficient H ha hi order hc) (innerCoefficient H ha hi order hc hlt)
      (orderedGraph H ha hi hlt) =
    GraphGeneralWeightedGraft.graftProfile (physicalSlot hlt hsize)
      (rawBinaryWeight (coarseN i S + 1)) (rawBinaryWeight (shapeN a S + 1))
      (H.reindexForGraft (o := 1) (l := 1) (anchoredPartitionEquiv ha hi) (Equiv.refl _)) := by
  apply graftProfile_reindex_binary (outsideM_eq_one hsize) (by omega)
  · intro G
    exact canonicalWeight_eq_raw_cast (by rw [outsideM_eq_one hsize]) G _
  · intro G
    exact canonicalWeight_inner_eq_raw_cast hsize G _ (by omega)
  · intro j
    rfl

theorem anchoredCount (ha : a ∈ S) (hi : i ∉ S) :
    (coarseN i S + 1) + (shapeN a S + 1) = n := by
  simpa using Fintype.card_congr (anchoredPartitionEquiv ha hi)

def anchoredPermutation (ha : a ∈ S) (hi : i ∉ S) :
    Equiv.Perm (Fin ((coarseN i S + 1) + (shapeN a S + 1))) :=
  (anchoredPartitionEquiv ha hi).trans (finCongr (anchoredCount ha hi)).symm

def physicalCluster (ha : a ∈ S) (hi : i ∉ S) :
    Clusters (innerBlock (coarseN i S + 1) (shapeN a S + 1)) :=
  movedCluster _ (anchoredPermutation ha hi)

theorem anchoredPartition_mem_iff (ha : a ∈ S) (hi : i ∉ S)
    (v : Fin ((coarseN i S + 1) + (shapeN a S + 1))) :
    anchoredPartitionEquiv ha hi v ∈ S ↔ v ∈ innerBlock (coarseN i S + 1) (shapeN a S + 1) := by
  refine Fin.addCases (fun v ↦ ?_) (fun v ↦ ?_) v
  · rw [anchoredPartition_outer]
    exact iff_of_false ((coarseSourceEquiv hi).symm v).property (outerIndexEquiv _ _ v).property
  · rw [anchoredPartition_inner]
    exact iff_of_true ((shapeSourceEquiv ha).symm v).property (innerIndexEquiv _ _ v).property

/-- The chosen cluster really is the original physical subset, with only
the cardinality cast needed by the global finite cluster sum. -/
theorem physicalCluster_mem (ha : a ∈ S) (hi : i ∉ S)
    (v : Fin ((coarseN i S + 1) + (shapeN a S + 1))) :
    v ∈ (physicalCluster ha hi).val ↔ finCongr (anchoredCount ha hi) v ∈ S := by
  obtain ⟨v,rfl⟩ := (anchoredPermutation ha hi).surjective v
  have hm := (movedCluster_eq_iff _ _ (physicalCluster ha hi)).mp rfl v
  rw [hm]
  have hc : finCongr (anchoredCount ha hi) (anchoredPermutation ha hi v) =
      anchoredPartitionEquiv ha hi v := by simp [anchoredPermutation]
  rw [hc]
  exact (anchoredPartition_mem_iff ha hi v).symm

theorem canonical_graft_eq_rawCluster (hlt : l < u) (hsize : shapeM l u = 2) :
    GraphGeneralWeightedGraft.graftProfile (centerSlot hlt.le)
      (outerCoefficient H ha hi order hc) (innerCoefficient H ha hi order hc hlt)
      (orderedGraph H ha hi hlt) =
    rawClusterCoefficient (physicalSlot hlt hsize)
      (GraphAssociatorProfiles.castVertices (anchoredCount ha hi).symm H) (physicalCluster ha hi) := by
  rw [canonical_graft_eq_raw_native H ha hi order hc hlt hsize]
  symm
  apply GraphBinaryClusterNativeMatching.rawClusterCoefficient_eq_native_graftProfile_of_count
  exact (movedCluster_eq_iff _ _ (physicalCluster ha hi)).mp rfl

/-- Any global cluster-subset representation with the correct original
memberships gives exactly the same coefficient. -/
theorem canonical_graft_eq_rawCluster_of_membership (hlt : l < u) (hsize : shapeM l u = 2)
    (T : Clusters (innerBlock (coarseN i S + 1) (shapeN a S + 1)))
    (hT : ∀ v, v ∈ T.val ↔ finCongr (anchoredCount ha hi) v ∈ S) :
    GraphGeneralWeightedGraft.graftProfile (centerSlot hlt.le)
      (outerCoefficient H ha hi order hc) (innerCoefficient H ha hi order hc hlt)
      (orderedGraph H ha hi hlt) =
    rawClusterCoefficient (physicalSlot hlt hsize)
      (GraphAssociatorProfiles.castVertices (anchoredCount ha hi).symm H) T := by
  have ht : T = physicalCluster ha hi := by
    apply Subtype.ext
    apply Finset.ext
    intro v
    exact (hT v).trans (physicalCluster_mem ha hi v).symm
  subst T
  exact canonical_graft_eq_rawCluster H ha hi order hc hlt hsize

theorem shapeCount_eq_card (ha : a ∈ S) : shapeN a S + 1 = S.card := by
  simpa using (Fintype.card_congr (shapeSourceEquiv ha)).symm

theorem coarseCount_eq_card_compl (hi : i ∉ S) : coarseN i S + 1 = n - S.card := by
  simpa [Fintype.card_subtype_compl] using (Fintype.card_congr (coarseSourceEquiv hi)).symm

@[simp] theorem physicalSlot_slotZero (hsize : shapeM (0 : Fin 4) 2 = 2) :
    physicalSlot (show (0 : Fin 4) < 2 by decide) hsize = 0 := by
  apply Fin.ext
  rfl

@[simp] theorem physicalSlot_slotOne (hsize : shapeM (1 : Fin 4) 3 = 2) :
    physicalSlot (show (1 : Fin 4) < 3 by decide) hsize = 1 := by
  apply Fin.ext
  rfl

end Actual
end EnvelopingIsomorphism.Deformation.Kontsevich.MainRealGraftPhysicalCoefficient
