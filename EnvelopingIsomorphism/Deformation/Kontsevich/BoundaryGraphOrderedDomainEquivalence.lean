import EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryGraphOrderedDomains

/-! Exact product-domain correspondence for the ordered real-cluster face coordinates. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryGraphOrderedCoordinates
open Configuration BoundaryGraphFaceFactorization
open scoped BigOperators Classical
variable {n m : ℕ} {i a : Fin n} {S : Finset (Fin n)} {l u : Fin (m + 1)}

theorem shapeOrderedEnum_lt_iff (j k : ShapeBoundary l u) :
    shapeOrderedEnum l u j < shapeOrderedEnum l u k ↔ j.val < k.val := by
  have h := shapeOrderedEnum_symm_strictMono.lt_iff_lt
    (a := shapeOrderedEnum l u j) (b := shapeOrderedEnum l u k)
  simpa only [Equiv.symm_apply_apply] using h.symm

theorem outsideOrderedEnum_lt_iff (j k : OutsideBoundary l u) :
    outsideOrderedEnum l u j < outsideOrderedEnum l u k ↔ j.val < k.val := by
  have h := outsideOrderedEnum_symm_strictMono.lt_iff_lt
    (a := outsideOrderedEnum l u j) (b := outsideOrderedEnum l u k)
  simpa only [Equiv.symm_apply_apply] using h.symm

theorem ordered_shape_interior (hlu : l ≤ u) (y : FaceCoordinates i a S m) (j : Fin n) (hj : j ∈ S) :
    GraphForms.interiorPoint (shapeSource (a := a) j hj) (orderedSplitFace hlu y).1 =
      (BoundaryClusterFreeCoordinates.faceEmbedding y).velocity j := by
  rw [orderedSplitFace_fst, interiorPoint_boundaryCoordinates]
  exact shapeSource_position y j hj

theorem ordered_coarse_interior (hlu : l ≤ u) (y : FaceCoordinates i a S m) (j : Fin n) (hj : j ∉ S) :
    GraphForms.interiorPoint (coarseSource (i := i) j hj) (orderedSplitFace hlu y).2 =
      (BoundaryClusterFreeCoordinates.faceEmbedding y).base j := by
  rw [orderedSplitFace_snd, interiorPoint_boundaryCoordinates]
  exact coarseSource_position y j hj

theorem faceOpenConditions_of_ordered_admissible (ha : a ∈ S) (hi : i ∉ S) (hlu : l ≤ u)
    (y : FaceCoordinates i a S m)
    (hshape : GraphForms.Admissible (orderedSplitFace hlu y).1)
    (hcoarse : GraphForms.Admissible (orderedSplitFace hlu y).2) :
    (BoundaryClusterFreeCoordinates.faceEmbedding y).OpenConditions l u := by
  let x := BoundaryClusterFreeCoordinates.faceEmbedding y
  have hsp (j : Fin n) (hj : j ∈ S) : 0 < (x.velocity j).im := by
    rw [← ordered_shape_interior hlu y j hj]
    exact hshape.interiorPoint_im_pos _
  have hcp (j : Fin n) (hj : j ∉ S) : 0 < (x.base j).im := by
    rw [← ordered_coarse_interior hlu y j hj]
    exact hcoarse.interiorPoint_im_pos _
  have hsi (j k : Fin n) (hj : j ∈ S) (hk : k ∈ S) (h : x.velocity j = x.velocity k) : j = k := by
    have he : shapeSource (a := a) j hj = shapeSource (a := a) k hk := by
      apply hshape.2.1
      simpa only [ordered_shape_interior] using h
    have he' : shapeSourceEquiv ha ⟨j,hj⟩ = shapeSourceEquiv ha ⟨k,hk⟩ := he
    exact congrArg Subtype.val ((shapeSourceEquiv ha).injective he')
  have hci (j k : Fin n) (hj : j ∉ S) (hk : k ∉ S) (h : x.base j = x.base k) : j = k := by
    have he : coarseSource (i := i) j hj = coarseSource (i := i) k hk := by
      apply hcoarse.2.1
      simpa only [ordered_coarse_interior] using h
    have he' : coarseSourceEquiv hi ⟨j,hj⟩ = coarseSourceEquiv hi ⟨k,hk⟩ := he
    exact congrArg Subtype.val ((coarseSourceEquiv hi).injective he')
  have hl (j : Fin m) (hj : j.val < l.val) : x.boundaryBase l u j < x.center := by
    have hjo : j ∉ boundaryClusterBlock l u := by simp only [mem_boundaryClusterBlock]; omega
    let v := outsideOrderedEnum l u ⟨j,hjo⟩
    have hv : v.val < l.val := by dsimp [v]; rw [outsideOrderedEnum_val hlu, if_pos hj]; exact hj
    have h := hcoarse.2.2 ((succAbove_lt_center_iff hlu v).mpr hv)
    change (orderedSplitFace hlu y).2.2 ((centerSlot hlu).succAbove v) < (orderedSplitFace hlu y).2.2 (centerSlot hlu) at h
    rw [ordered_coarse_center] at h
    dsimp only [v] at h
    rw [ordered_coarse_outside] at h
    simpa [x, BoundaryClusterFreeCoordinates.boundaryBase, hjo,
      BoundaryClusterFreeCoordinates.center, BoundaryClusterFreeCoordinates.faceEmbedding] using h
  have hr (j : Fin m) (hj : u.val ≤ j.val) : x.center < x.boundaryBase l u j := by
    have hjo : j ∉ boundaryClusterBlock l u := by simp only [mem_boundaryClusterBlock]; omega
    let v := outsideOrderedEnum l u ⟨j,hjo⟩
    have hv : l.val ≤ v.val := by
      dsimp [v]
      rw [outsideOrderedEnum_val hlu]
      change l.val ≤ (if j.val < l.val then j.val else j.val - (u.val - l.val))
      rw [if_neg (by have h : l.val ≤ u.val := hlu; omega)]
      have h : l.val ≤ u.val := hlu
      omega
    have h := hcoarse.2.2 ((center_lt_succAbove_iff hlu v).mpr hv)
    change (orderedSplitFace hlu y).2.2 (centerSlot hlu) < (orderedSplitFace hlu y).2.2 ((centerSlot hlu).succAbove v) at h
    rw [ordered_coarse_center] at h
    dsimp only [v] at h
    rw [ordered_coarse_outside] at h
    simpa [x, BoundaryClusterFreeCoordinates.boundaryBase, hjo,
      BoundaryClusterFreeCoordinates.center, BoundaryClusterFreeCoordinates.faceEmbedding] using h
  have hbb (j k : Fin m) (hjk : j < k)
      (hnot : ¬(j ∈ boundaryClusterBlock l u ∧ k ∈ boundaryClusterBlock l u)) :
      x.boundaryBase l u j < x.boundaryBase l u k := by
    by_cases hj : j ∈ boundaryClusterBlock l u
    · have hk : k ∉ boundaryClusterBlock l u := fun hk ↦ hnot ⟨hj,hk⟩
      have hku : u.val ≤ k.val := by
        have hjb := (mem_boundaryClusterBlock l u j).mp hj
        simp only [mem_boundaryClusterBlock] at hk
        have hjk' : j.val < k.val := hjk
        omega
      rw [BoundaryClusterFreeCoordinates.boundaryBase_eq_center x l u j hj]
      exact hr k hku
    · by_cases hk : k ∈ boundaryClusterBlock l u
      · have hjl : j.val < l.val := by
          have hkb := (mem_boundaryClusterBlock l u k).mp hk
          simp only [mem_boundaryClusterBlock] at hj
          have hjk' : j.val < k.val := hjk
          omega
        rw [BoundaryClusterFreeCoordinates.boundaryBase_eq_center x l u k hk]
        exact hl j hjl
      · have hlt := (outsideOrderedEnum_lt_iff (⟨j,hj⟩ : OutsideBoundary l u) ⟨k,hk⟩).mpr hjk
        have h := hcoarse.2.2 (Fin.strictMono_succAbove (centerSlot hlu) hlt)
        rw [ordered_coarse_outside, ordered_coarse_outside] at h
        simpa [x, BoundaryClusterFreeCoordinates.boundaryBase, hj, hk,
          BoundaryClusterFreeCoordinates.faceEmbedding] using h
  have hss (j k : Fin m) (hj : j ∈ boundaryClusterBlock l u) (hk : k ∈ boundaryClusterBlock l u)
      (hjk : j < k) : x.boundaryVelocity l u j < x.boundaryVelocity l u k := by
    have hlt := (shapeOrderedEnum_lt_iff (⟨j,hj⟩ : ShapeBoundary l u) ⟨k,hk⟩).mpr hjk
    have h := hshape.2.2 hlt
    rw [ordered_shape_boundary, ordered_shape_boundary] at h
    simpa [x, BoundaryClusterFreeCoordinates.boundaryVelocity, hj, hk,
      BoundaryClusterFreeCoordinates.faceEmbedding] using h
  have hbne (j k : Fin n) (hnot : ¬(j = k ∨ (j ∈ S ∧ k ∈ S))) : x.base j ≠ x.base k := by
    by_cases hj : j ∈ S
    · have hk : k ∉ S := fun hk ↦ hnot (Or.inr ⟨hj,hk⟩)
      intro he
      have hp := hcp k hk
      rw [← he, x.base_eq_center j hj, Complex.ofReal_im] at hp
      exact lt_irrefl _ hp
    · by_cases hk : k ∈ S
      · intro he
        have hp := hcp j hj
        rw [he, x.base_eq_center k hk, Complex.ofReal_im] at hp
        exact lt_irrefl _ hp
      · exact fun he ↦ hnot (Or.inl (hci j k hj hk he))
  refine ⟨?_, ?_⟩
  · exact ⟨ha, hi, hlu, hcp, (fun j k hj hk hne he ↦ hne (hci j k hj hk he)),
      hsp, (fun j k hj hk hne he ↦ hne (hsi j k hj hk he)), hl, hr, hbb, hss⟩
  · have hradius : x.radius = 0 := rfl
    constructor
    · intro j k hjk
      rw [hradius, zero_mul]
      exact norm_pos_iff.mpr (sub_ne_zero.mpr (hbne j k hjk))
    · intro j k hjk hnot
      rw [hradius, zero_mul]
      exact sub_pos.mpr (hbb j k hjk hnot)

theorem faceOpenConditions_iff_ordered_admissible (ha : a ∈ S) (hi : i ∉ S) (hlu : l ≤ u)
    (y : FaceCoordinates i a S m) :
    (BoundaryClusterFreeCoordinates.faceEmbedding y).OpenConditions l u ↔
      GraphForms.Admissible (orderedSplitFace hlu y).1 ∧ GraphForms.Admissible (orderedSplitFace hlu y).2 :=
  ⟨orderedSplitFace_admissible hlu y, fun h ↦ faceOpenConditions_of_ordered_admissible ha hi hlu y h.1 h.2⟩

theorem orderedSplitFace_image_domain (ha : a ∈ S) (hi : i ∉ S) (hlu : l ≤ u) :
    orderedSplitFace hlu '' {y : FaceCoordinates i a S m |
      (BoundaryClusterFreeCoordinates.faceEmbedding y).OpenConditions l u} =
      GraphForms.admissibleSet (shapeN a S) (shapeM l u) ×ˢ
        GraphForms.admissibleSet (coarseN i S) (outsideM l u + 1) := by
  have hs : {y : FaceCoordinates i a S m | (BoundaryClusterFreeCoordinates.faceEmbedding y).OpenConditions l u} =
      (orderedSplitFace hlu) ⁻¹' (GraphForms.admissibleSet (shapeN a S) (shapeM l u) ×ˢ
        GraphForms.admissibleSet (coarseN i S) (outsideM l u + 1)) := by
    ext y
    exact faceOpenConditions_iff_ordered_admissible ha hi hlu y
  rw [hs]
  exact Set.image_preimage_eq _ (orderedSplitFace hlu).surjective

end EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryGraphOrderedCoordinates
