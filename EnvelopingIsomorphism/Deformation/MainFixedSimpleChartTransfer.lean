import EnvelopingIsomorphism.Deformation.MainStaticCollisionChartTransfer
import EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryClusterPhase
import EnvelopingIsomorphism.Deformation.Kontsevich.PureBoundaryClusterCompactification
import EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryAnchoredInfinityInsertion

/-! Actual original-chart transfer for proper real, pure boundary, and
infinity collision data. All static-mask premises are discharged from the
primitive data; only actual chart target membership is needed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.MainFixedSimpleChartTransfer

open Kontsevich Configuration MainStaticCollisionChartTransfer
open ExtractedForestParameters ExtractedForestFrames ForestRadialFaceClassification
open scoped Classical

variable {n m : ℕ}

def collisionMask (S : Finset (Fin (n + 1))) (l u : Fin (m + 1)) :
    Finset (DoubledLabel (n + 1) m) := Finset.univ.filter (boundaryClusterCollapses S l u)

@[simp] theorem mem_collisionMask (S : Finset (Fin (n + 1))) (l u : Fin (m + 1))
    (v : DoubledLabel (n + 1) m) :
    v ∈ collisionMask S l u ↔ boundaryClusterCollapses S l u v := by simp [collisionMask]

theorem collisionMask_stable (S : Finset (Fin (n + 1))) (l u : Fin (m + 1)) :
    (collisionMask S l u).image doubledReflection = collisionMask S l u := by
  have hm (v : DoubledLabel (n + 1) m) :
      doubledReflection v ∈ collisionMask S l u ↔ v ∈ collisionMask S l u := by
    rcases v with (j | j) | j <;> simp [boundaryClusterCollapses, doubledReflection]
  ext v
  constructor
  · intro h
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp h
    exact (hm w).mpr hw
  · intro h
    exact Finset.mem_image.mpr ⟨doubledReflection v, (hm v).mpr h, doubledReflection_involutive v⟩

theorem interiorLabels_of_mask (x : Compactification (0 : Fin (n + 1)) m)
    (v : tree 0 x) (S : Finset (Fin (n + 1))) (l u : Fin (m + 1))
    (hv : v.val = collisionMask S l u) : ForestRadialClusterLabels.interiorLabels 0 x v = S := by
  ext j
  simp [ForestRadialClusterLabels.mem_interiorLabels, hv, boundaryClusterCollapses]

theorem boundaryLabels_of_mask (x : Compactification (0 : Fin (n + 1)) m)
    (v : tree 0 x) (S : Finset (Fin (n + 1))) (l u : Fin (m + 1))
    (hv : v.val = collisionMask S l u) :
    ForestRadialClusterLabels.boundaryLabels 0 x v = boundaryClusterBlock l u := by
  ext j
  simp [ForestRadialClusterLabels.mem_boundaryLabels, hv, boundaryClusterCollapses]

variable {r : ℕ} (hdim : GraphForms.dimension n m = r + 1)
  (x : Compactification (0 : Fin (n + 1)) m)

/-- Proper real collision transfer, retaining the full original doubled mask. -/
theorem properReal_source_changeAnchor {i a : Fin (n + 1)} {S : Finset (Fin (n + 1))} {l u : Fin (m + 1)}
    (D : BoundaryClusterData i a m S l u)
    (hq : anchorHomeomorph i 0 D.boundaryPoint ∈ (ForestOrthantCharts.chart 0 x).target) :
    ∃ (o : ForestRadialFaceClassification.Orbit 0 x)
      (z : ForestRadialFaceLocalization.source hdim x o),
      kind 0 x o = .properReal ∧ (representative 0 x o).val.val = collisionMask S l u ∧
      PairedForestSimpleOverlap.facePoint hdim x o z = anchorHomeomorph i 0 D.boundaryPoint := by
  have hlarge : 1 < (collisionMask S l u).card := Finset.one_lt_card.mpr
    ⟨Sum.inl (Sum.inl a), by simpa [boundaryClusterCollapses] using D.anchor_mem,
      Sum.inr a, by simpa [boundaryClusterCollapses] using D.anchor_mem, by simp⟩
  have hn : (Sum.inl (Sum.inl i) : DoubledLabel (n + 1) m) ∉ collisionMask S l u := by
    simpa [boundaryClusterCollapses] using D.normalized_not_mem
  have hproper : collisionMask S l u ≠ Finset.univ := fun he => hn (he.symm ▸ Finset.mem_univ _)
  have hbase (p : DoubledPair (n + 1) m) :
      D.doubledBase p.val.2 - D.doubledBase p.val.1 = 0 ↔
        p.val.1 ∈ collisionMask S l u ∧ p.val.2 ∈ collisionMask S l u := by
    change D.pairBase p = 0 ↔ _
    rw [D.pairBase_eq_zero_iff_boundaryClusterPairCollapses]
    simp [boundaryClusterPairCollapses]
  have hDR : projectDR (anchorHomeomorph i 0 D.boundaryPoint).val =
      projectDR (linearCollisionCoordinates D.doubledBase D.doubledVelocity) := by
    rw [projectDR_anchorHomeomorph]
    change projectDR (D.resolvedCoordinates 0) = _
    rw [D.resolvedCoordinates_zero]
  obtain ⟨o,z,hmask,hfixed,hpoint⟩ := exists_source_of_static_collision hdim x (anchorHomeomorph i 0 D.boundaryPoint)
    (collisionMask S l u) D.doubledBase D.doubledVelocity hbase
    D.pairVelocity_ne_zero_of_pairBase_eq_zero hlarge hproper (collisionMask_stable S l u) hDR hq
  refine ⟨o,z,?_,hmask,hpoint⟩
  rw [← kind_representative]
  apply (nodeKind_properReal_iff 0 x _).mpr
  refine ⟨hfixed,⟨a,?_⟩,⟨i,?_⟩⟩
  · rw [hmask]
    simpa [boundaryClusterCollapses] using D.anchor_mem
  · rw [hmask]
    exact hn

theorem properReal_source {a : Fin (n + 1)} {S : Finset (Fin (n + 1))} {l u : Fin (m + 1)}
    (D : BoundaryClusterData (0 : Fin (n + 1)) a m S l u)
    (hq : D.boundaryPoint ∈ (ForestOrthantCharts.chart 0 x).target) :
    ∃ (o : ForestRadialFaceClassification.Orbit 0 x)
      (z : ForestRadialFaceLocalization.source hdim x o),
      kind 0 x o = .properReal ∧ (representative 0 x o).val.val = collisionMask S l u ∧
      PairedForestSimpleOverlap.facePoint hdim x o z = D.boundaryPoint := by
  simpa only [anchorHomeomorph_refl, Homeomorph.refl_apply, id_eq] using
    properReal_source_changeAnchor hdim x D
      (by simpa only [anchorHomeomorph_refl, Homeomorph.refl_apply, id_eq] using hq)

/-- Pure boundary collision transfer, with no interior labels in its mask. -/
theorem pureBoundary_source {a b : Fin m} {l u : Fin (m + 1)}
    (D : PureBoundaryClusterData (0 : Fin (n + 1)) m l u a b)
    (hq : D.boundaryPoint ∈ (ForestOrthantCharts.chart 0 x).target) :
    ∃ (o : ForestRadialFaceClassification.Orbit 0 x)
      (z : ForestRadialFaceLocalization.source hdim x o),
      kind 0 x o = .pureBoundary ∧ (representative 0 x o).val.val = collisionMask ∅ l u ∧
      PairedForestSimpleOverlap.facePoint hdim x o z = D.boundaryPoint := by
  have hlarge : 1 < (collisionMask (n := n) ∅ l u).card := Finset.one_lt_card.mpr
    ⟨Sum.inl (Sum.inr a), by simpa [boundaryClusterCollapses] using D.left_mem,
      Sum.inl (Sum.inr b), by simpa [boundaryClusterCollapses] using D.right_mem,
      fun he => D.endpoint_lt.ne (Sum.inr.inj (Sum.inl.inj he))⟩
  have hn : (Sum.inl (Sum.inl (0 : Fin (n + 1))) : DoubledLabel (n + 1) m) ∉ collisionMask ∅ l u := by
    simp [boundaryClusterCollapses]
  have hproper : collisionMask (n := n) ∅ l u ≠ Finset.univ := fun he => hn (he.symm ▸ Finset.mem_univ _)
  have hpred (v : DoubledLabel (n + 1) m) : pureBoundaryClusterCollapses l u v ↔
      v ∈ collisionMask (n := n) ∅ l u := by
    rcases v with (j | j) | j <;> simp [pureBoundaryClusterCollapses, boundaryClusterCollapses]
  have hbase (p : DoubledPair (n + 1) m) :
      D.doubledBase p.val.2 - D.doubledBase p.val.1 = 0 ↔
        p.val.1 ∈ collisionMask (n := n) ∅ l u ∧ p.val.2 ∈ collisionMask (n := n) ∅ l u := by
    change D.pairBase p = 0 ↔ _
    rw [D.pairBase_eq_zero_iff_pureBoundaryClusterPairCollapses]
    exact and_congr (hpred _) (hpred _)
  have hDR : projectDR D.boundaryPoint.val = projectDR (linearCollisionCoordinates D.doubledBase D.doubledVelocity) := by
    change projectDR (D.resolvedCoordinates 0) = _
    rw [D.resolvedCoordinates_zero]
  obtain ⟨o,z,hmask,hfixed,hpoint⟩ := exists_source_of_static_collision hdim x D.boundaryPoint
    (collisionMask ∅ l u) D.doubledBase D.doubledVelocity hbase
    D.pairVelocity_ne_zero_of_pairBase_eq_zero hlarge hproper (collisionMask_stable ∅ l u) hDR hq
  refine ⟨o,z,?_,hmask,hpoint⟩
  rw [← kind_representative]
  apply (nodeKind_pureBoundary_iff 0 x _).mpr
  refine ⟨hfixed,?_⟩
  intro j
  rw [hmask]
  simp [boundaryClusterCollapses]

/-- Infinity transfer uses the actual boundary-anchored insertion, including
its recovered infinite position coordinates in the interior-anchor chart. -/
theorem infinity_source {l u : Fin (m + 1)} {a : Fin m}
    (D : BoundaryAnchoredInfinityData (0 : Fin (n + 1)) m l u a)
    (hq : D.compactInsertion D.admissibleScale_zero ∈ (ForestOrthantCharts.chart 0 x).target) :
    ∃ (o : ForestRadialFaceClassification.Orbit 0 x)
      (z : ForestRadialFaceLocalization.source hdim x o),
      kind 0 x o = .infinity ∧ (representative 0 x o).val.val = collisionMask Finset.univ l u ∧
      PairedForestSimpleOverlap.facePoint hdim x o z = D.compactInsertion D.admissibleScale_zero := by
  have hlarge : 1 < (collisionMask (n := n) Finset.univ l u).card := Finset.one_lt_card.mpr
    ⟨Sum.inl (Sum.inl 0), by simp [boundaryClusterCollapses],
      Sum.inr 0, by simp [boundaryClusterCollapses], by simp⟩
  have hn : (Sum.inl (Sum.inr a) : DoubledLabel (n + 1) m) ∉ collisionMask Finset.univ l u := by
    simpa [boundaryClusterCollapses] using D.outside_not_mem
  have hproper : collisionMask (n := n) Finset.univ l u ≠ Finset.univ := fun he => hn (he.symm ▸ Finset.mem_univ _)
  have hpred (v : DoubledLabel (n + 1) m) : boundaryAnchoredInfinityCollapses l u v ↔
      v ∈ collisionMask (n := n) Finset.univ l u := by
    rcases v with (j | j) | j <;> simp [boundaryAnchoredInfinityCollapses, boundaryClusterCollapses]
  have hbase (p : DoubledPair (n + 1) m) :
      D.doubledBase p.val.2 - D.doubledBase p.val.1 = 0 ↔
        p.val.1 ∈ collisionMask (n := n) Finset.univ l u ∧ p.val.2 ∈ collisionMask (n := n) Finset.univ l u := by
    change D.pairBase p = 0 ↔ _
    rw [D.pairBase_eq_zero_iff_pairCollapses]
    exact and_congr (hpred _) (hpred _)
  have hDR : projectDR (D.compactInsertion D.admissibleScale_zero).val =
      projectDR (linearCollisionCoordinates D.doubledBase D.doubledVelocity) := by
    rw [D.compactInsertion_projectDR, D.resolvedDR_zero]
  obtain ⟨o,z,hmask,hfixed,hpoint⟩ := exists_source_of_static_collision hdim x
    (D.compactInsertion D.admissibleScale_zero) (collisionMask Finset.univ l u)
    D.doubledBase D.doubledVelocity hbase D.pairVelocity_ne_zero_of_pairBase_eq_zero
    hlarge hproper (collisionMask_stable Finset.univ l u) hDR hq
  refine ⟨o,z,?_,hmask,hpoint⟩
  rw [← kind_representative]
  apply (nodeKind_infinity_iff 0 x _).mpr
  refine ⟨hfixed,?_⟩
  intro j
  rw [hmask]
  simp [boundaryClusterCollapses]

end EnvelopingIsomorphism.Deformation.MainFixedSimpleChartTransfer
