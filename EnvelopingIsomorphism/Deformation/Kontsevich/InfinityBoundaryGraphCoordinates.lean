import EnvelopingIsomorphism.Deformation.Kontsevich.InfinityBoundaryGraphFactorization
import EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryGraphOrderedDomains

/-! Exact shape coordinates for the surviving infinity face with one outside
boundary label. The original outside anchor has no remaining free coordinate. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.InfinityBoundaryGraphCoordinates
open scoped Classical
open BoundaryAnchoredInfinityFreeCoordinates InfinityBoundaryGraphFactorization
open BoundaryGraphOrderedCoordinates
variable {n m : ℕ} {a : Fin n} {o : Fin m} {l u : Fin (m+1)}

def sourceEquiv : Fin n ≃ Fin (shapeN a + 1) where
  toFun := source
  invFun j := Fin.cases a (fun k ↦ (interiorEnum.symm k).val) j
  left_inv j := by
    by_cases hj : j = a <;> simp [source, hj]
  right_inv j := by
    cases j using Fin.cases with
    | zero => simp [source]
    | succ j => simp [source, (interiorEnum.symm j).property]

/-- Every non-anchor real coordinate is an inner shape coordinate. -/
def shapeEquiv (ho : o ∉ boundaryClusterBlock l u)
    (hall : ∀ j : Fin m, j ≠ o → j ∈ boundaryClusterBlock l u) :
    FaceCoordinates a m o ≃L[ℝ] Shape a l u :=
  { shapeCoordinates ho with
    invFun := fun z ↦ (fun j ↦ z.1 (interiorEnum j),
      fun j ↦ z.2 (shapeOrderedEnum l u ⟨j.val, hall j.val j.property⟩))
    left_inv := by
      intro y
      apply Prod.ext
      · funext j
        simp [shapeCoordinates]
      · funext j
        simp [shapeCoordinates]
    right_inv := by
      intro z
      apply Prod.ext
      · funext j
        simp [shapeCoordinates]
      · funext j
        simp [shapeCoordinates] }

theorem boundary_position (ho : o ∉ boundaryClusterBlock l u)
    (y : FaceCoordinates a m o) (j : Fin m) (hj : j ∈ boundaryClusterBlock l u) :
    (shapeCoordinates ho y).2 (shapeOrderedEnum l u ⟨j,hj⟩) =
      (faceEmbedding y).boundaryVelocity l u j := by
  exact Complex.ofReal_injective (target_position ho y (Sum.inr j) hj)

theorem shape_admissible (ho : o ∉ boundaryClusterBlock l u)
    (y : FaceCoordinates a m o) (hy : (faceEmbedding y).OpenConditions l u) :
    GraphForms.Admissible (shapeCoordinates ho y) := by
  let x := faceDomain y hy
  refine ⟨?_, ?_, ?_⟩
  · intro j
    simpa [x, faceDomain, shape, shapeCoordinates, (interiorEnum.symm j).property]
      using x.shape_im_pos (interiorEnum.symm j).val
  · intro j k h
    obtain ⟨j,rfl⟩ := (sourceEquiv (a := a)).surjective j
    obtain ⟨k,rfl⟩ := (sourceEquiv (a := a)).surjective k
    apply sourceEquiv.injective.eq_iff.mpr
    apply x.datum.shape_injective
    apply UpperHalfPlane.ext
    simpa only [sourceEquiv, Equiv.coe_fn_mk, source_position, BoundaryAnchoredInfinityFreeDomain.datum_shape, x, faceDomain] using h
  · intro j k hjk
    have hj := ((shapeOrderedEnum l u).symm j).property
    have hk := ((shapeOrderedEnum l u).symm k).property
    have h := x.datum.boundaryVelocity_strictMono_on _ _ hj hk (shapeOrderedEnum_symm_strictMono hjk)
    rw [BoundaryAnchoredInfinityFreeDomain.datum_boundaryVelocity,
      BoundaryAnchoredInfinityFreeDomain.datum_boundaryVelocity] at h
    change (faceEmbedding y).boundaryVelocity l u _ < (faceEmbedding y).boundaryVelocity l u _ at h
    simpa only [← boundary_position ho y _ hj, ← boundary_position ho y _ hk, Subtype.coe_eta, Equiv.apply_symm_apply] using h

/-- Any other outside label would contradict the selected full-degree count. -/
theorem onlyOutside_of_card (ho : o ∉ boundaryClusterBlock l u)
    (hcard : (boundaryClusterBlock l u).card = m - 1) :
    ∀ j : Fin m, j ≠ o → j ∈ boundaryClusterBlock l u := by
  have hs : boundaryClusterBlock l u ⊆ Finset.univ.erase o := by
    intro j hj
    exact Finset.mem_erase.mpr ⟨fun h ↦ ho (h ▸ hj), Finset.mem_univ _⟩
  have he : boundaryClusterBlock l u = Finset.univ.erase o :=
    Finset.eq_of_subset_of_card_le hs (by simp [hcard])
  intro j hj
  simp [he, hj]

/-- Exact converse: the surviving one-outside-label face has precisely the
ordinary normalized shape chamber, including all scale-zero inequalities. -/
theorem face_open_of_admissible (hlu : l ≤ u) (ho : o ∉ boundaryClusterBlock l u)
    (hall : ∀ j : Fin m, j ≠ o → j ∈ boundaryClusterBlock l u)
    (y : FaceCoordinates a m o) (hy : GraphForms.Admissible (shapeCoordinates ho y)) :
    (faceEmbedding y).OpenConditions l u := by
  let x := faceEmbedding y
  have honly (j : Fin m) (hj : j ∉ boundaryClusterBlock l u) : j = o := by
    by_contra hn
    exact hj (hall j hn)
  have hpos (j : Fin n) : 0 < (x.shape j).im := by
    rw [← source_position ho y j]
    exact hy.interiorPoint_im_pos _
  have hinj (j k : Fin n) (he : x.shape j = x.shape k) : j = k := by
    apply (sourceEquiv (a := a)).injective
    apply hy.2.1
    simpa only [sourceEquiv, Equiv.coe_fn_mk, source_position] using he
  have hleft (j : Fin m) (hj : j.val < l.val) : x.boundaryBase l u j < 0 := by
    have hn : j ∉ boundaryClusterBlock l u := by simp only [mem_boundaryClusterBlock]; omega
    have he := honly j hn
    subst j
    simp [boundaryBase, ho, boundaryCoordinate, BoundaryAnchoredInfinityData.referenceSign, hj]
  have hright (j : Fin m) (hj : u.val ≤ j.val) : 0 < x.boundaryBase l u j := by
    have hn : j ∉ boundaryClusterBlock l u := by simp only [mem_boundaryClusterBlock]; omega
    have he := honly j hn
    subst j
    have hl : ¬ o.val < l.val := by have hle : l.val ≤ u.val := hlu; omega
    simp [boundaryBase, ho, boundaryCoordinate, BoundaryAnchoredInfinityData.referenceSign, hl]
  have hbase (j k : Fin m) (hjk : j < k)
      (hnot : ¬ (j ∈ boundaryClusterBlock l u ∧ k ∈ boundaryClusterBlock l u)) :
      x.boundaryBase l u j < x.boundaryBase l u k := by
    by_cases hj : j ∈ boundaryClusterBlock l u
    · have hk : k ∉ boundaryClusterBlock l u := fun hk ↦ hnot ⟨hj,hk⟩
      have hj' := (mem_boundaryClusterBlock l u j).mp hj
      have hk' : ¬ (l.val ≤ k.val ∧ k.val < u.val) := by simpa only [mem_boundaryClusterBlock] using hk
      have hlt : j.val < k.val := hjk
      have h := hright k (by omega)
      simpa [boundaryBase, hj, hk] using h
    · by_cases hk : k ∈ boundaryClusterBlock l u
      · have hk' := (mem_boundaryClusterBlock l u k).mp hk
        have hj' : ¬ (l.val ≤ j.val ∧ j.val < u.val) := by simpa only [mem_boundaryClusterBlock] using hj
        have hlt : j.val < k.val := hjk
        have h := hleft j (by omega)
        simpa [boundaryBase, hj, hk] using h
      · have he : j = k := (honly j hj).trans (honly k hk).symm
        exact (hjk.ne he).elim
  have hshape (j k : Fin m) (hj : j ∈ boundaryClusterBlock l u)
      (hk : k ∈ boundaryClusterBlock l u) (hjk : j < k) :
      x.boundaryVelocity l u j < x.boundaryVelocity l u k := by
    rw [← boundary_position ho y j hj, ← boundary_position ho y k hk]
    apply hy.2.2
    apply (shapeOrderedEnum_symm_strictMono (l := l) (u := u)).lt_iff_lt.mp
    simpa using hjk
  refine ⟨⟨hlu, ho, hpos, fun j k hjk he ↦ hjk (hinj j k he), hleft, hright, hbase, hshape⟩, ?_⟩
  intro j k hjk hnot
  change (0 : ℝ) * _ < _
  rw [zero_mul]
  exact sub_pos.mpr (hbase j k hjk hnot)

theorem face_open_iff_admissible (hlu : l ≤ u) (ho : o ∉ boundaryClusterBlock l u)
    (hall : ∀ j : Fin m, j ≠ o → j ∈ boundaryClusterBlock l u) (y : FaceCoordinates a m o) :
    (faceEmbedding y).OpenConditions l u ↔ GraphForms.Admissible (shapeCoordinates ho y) :=
  ⟨shape_admissible ho y, face_open_of_admissible hlu ho hall y⟩

end EnvelopingIsomorphism.Deformation.Kontsevich.InfinityBoundaryGraphCoordinates
