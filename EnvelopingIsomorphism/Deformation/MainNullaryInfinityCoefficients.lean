import EnvelopingIsomorphism.Deformation.MainNullaryGraphCoefficients

/-! The all-interior infinity graph is the literal inner graph in the
full-subset graft fibre, in its actual anchored shape labels. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace EnvelopingIsomorphism.Deformation.MainNullaryInfinityCoefficients
open scoped Classical
open Kontsevich KontsevichGraph.General UniformBinaryGraphs
open GraphBinaryPhysicalSubsetIndex GraphBinaryClusterSums GraphLabelledClusterCounting
open GraphBinaryClusterNativeMatching GraphCanonicalBinaryWeights
open BoundaryGraphFaceFactorization BoundaryGraphOrderedCoordinates
open MainNullaryGraphCoefficients

variable {N B : ℕ}

theorem coefficient_full_eq_native (H : BinaryGraph N 3) (r : Fin 2)
    (h : 0+B = N) (e : Fin (0+B) ≃ Fin N) :
    coefficient H r Finset.univ =
      GraphGeneralWeightedGraft.graftProfile r (rawBinaryWeight 0) (rawBinaryWeight B)
        (H.reindexForGraft (o := 1) (l := 1) e (Equiv.refl _)) := by
  rw [coefficient_eq_of_count h H r ⟨innerBlock 0 B,rfl⟩ Finset.univ (by
    have hi : innerBlock 0 B = Finset.univ := by apply Finset.eq_univ_of_card; simp
    rw [hi]; exact Finset.map_univ_equiv _)]
  apply rawClusterCoefficient_eq_native_graftProfile_of_count h
  intro v
  have hi : innerBlock 0 B = Finset.univ := by apply Finset.eq_univ_of_card; simp
  simp [hi]

variable {l u : Fin 4}

theorem shapeOrderedEnum_offset (hlu : l ≤ u) (j : ShapeBoundary l u) :
    l.val + (shapeOrderedEnum l u j).val = j.val.val := by
  have hs := shapeM_eq_sub hlu
  have hl : l.val ≤ u.val := hlu
  let f : Fin (shapeM l u) → Fin 3 := fun k ↦ ⟨l.val+k.val,by have hk := k.isLt; have hu := u.isLt; omega⟩
  have hf : ∀ k, f k ∈ boundaryClusterBlock l u := by
    intro k
    have hk := k.isLt
    simp only [mem_boundaryClusterBlock,f]
    omega
  have hmono : StrictMono f := by intro i k hik; change l.val+i.val < l.val+k.val; exact Nat.add_lt_add_left hik _
  have he := Finset.orderEmbOfFin_unique (by exact (Fintype.card_coe (boundaryClusterBlock l u)).symm) hf hmono
  have hev := congrArg (fun g ↦ (g (shapeOrderedEnum l u j)).val) he
  change _ = ((shapeOrderedEnum l u).symm (shapeOrderedEnum l u j)).val.val at hev
  simpa only [Equiv.symm_apply_apply,f] using hev

open InfinityBoundaryGraphMatching

variable {n : ℕ} {a : Fin n}

def shapeLabels : Fin (0+(InfinityBoundaryGraphFactorization.shapeN a+1)) ≃ Fin n :=
  (finCongr (Nat.zero_add _)).trans InfinityBoundaryGraphCoordinates.sourceEquiv.symm

theorem shape_count : 0+(InfinityBoundaryGraphFactorization.shapeN a+1) = n := by
  exact Fintype.card_fin _ |>.symm.trans ((Fintype.card_congr (shapeLabels (a := a))).trans (Fintype.card_fin _))

def shapeNative (H : BinaryGraph n 3) :=
  H.reindexForGraft (o := 1) (l := 1) (shapeLabels (a := a)) (Equiv.refl _)

def binaryShape (hsize : shapeM l u = 2) (H : BinaryGraph n 3)
    (hin : ∀ e, boundaryAnchoredInfinityCollapses l u (Sum.inl (H.target e))) :
    BinaryGraph (InfinityBoundaryGraphFactorization.shapeN a+1) 2 :=
  (shapeGraph (a := a) H hin).reindex (Equiv.refl _) (finCongr hsize.symm)

theorem innerBoundary_shapeTarget (hlu : l ≤ u) (hsize : shapeM l u = 2)
    (j : ShapeBoundary l u) :
    graftInnerBoundary (l := 1) (slot hlu hsize) (Fin.cast hsize (shapeOrderedEnum l u j)) = j.val := by
  apply Fin.ext
  exact shapeOrderedEnum_offset hlu j

theorem binaryShape_target_embedding (hlu : l ≤ u) (hsize : shapeM l u = 2)
    (H : BinaryGraph n 3)
    (hin : ∀ e, boundaryAnchoredInfinityCollapses l u (Sum.inl (H.target e)))
    (v : Fin (InfinityBoundaryGraphFactorization.shapeN a+1)) (j : Fin 2) :
    graftInnerVertex (a := 0) (l := 1) (slot hlu hsize)
      ((binaryShape (a := a) hsize H hin).target ⟨v,j⟩) =
    (shapeNative (a := a) H).target
      (graftInnerEdge (fun _ : Fin 0 ↦ 2) (fun _ : Fin (InfinityBoundaryGraphFactorization.shapeN a+1) ↦ 2) ⟨v,j⟩) := by
  have htgt := Graph.reindexForGraft_target_inner (o := 1) (l := 1) H (shapeLabels (a := a)) (Equiv.refl (Fin 3)) v j
  change (shapeNative (a := a) H).target
      (graftInnerEdge (fun _ : Fin 0 ↦ 2) (fun _ : Fin (InfinityBoundaryGraphFactorization.shapeN a+1) ↦ 2) ⟨v,j⟩) = _ at htgt
  rw [htgt]
  change graftInnerVertex (a := 0) (l := 1) (slot hlu hsize)
    ((Equiv.sumCongr (Equiv.refl _) (finCongr hsize))
      (InfinityBoundaryGraphFactorization.shapeTarget
        (H.target ⟨InfinityBoundaryGraphCoordinates.sourceEquiv.symm v,j⟩) _)) = _
  have he : shapeLabels (a := a) (Fin.natAdd 0 v) = InfinityBoundaryGraphCoordinates.sourceEquiv.symm v := by
    apply congrArg InfinityBoundaryGraphCoordinates.sourceEquiv.symm
    apply Fin.ext
    simp
  rw [he]
  have lift : ∀ (x : Fin n ⊕ Fin 3)
      (hx : boundaryAnchoredInfinityCollapses l u (Sum.inl x)),
      graftInnerVertex (a := 0) (l := 1) (slot hlu hsize)
        ((Equiv.sumCongr (Equiv.refl _) (finCongr hsize))
          (InfinityBoundaryGraphFactorization.shapeTarget (a := a) x hx)) =
        (Equiv.sumCongr (shapeLabels (a := a)).symm (Equiv.refl (Fin 3))) x := by
    intro x hx
    cases x with
    | inl w =>
      apply congrArg Sum.inl
      apply Fin.ext
      simp [shapeLabels, InfinityBoundaryGraphCoordinates.sourceEquiv]
    | inr w =>
      change Sum.inr (graftInnerBoundary (l := 1) (slot hlu hsize)
        (Fin.cast hsize (shapeOrderedEnum l u ⟨w,hx⟩))) = Sum.inr w
      rw [innerBoundary_shapeTarget hlu hsize]
  exact lift _ _

theorem shape_innerClosed (hlu : l ≤ u) (hsize : shapeM l u = 2)
    (H : BinaryGraph n 3)
    (hin : ∀ e, boundaryAnchoredInfinityCollapses l u (Sum.inl (H.target e))) :
    (shapeNative (a := a) H).InnerClosed (l := 1) (slot hlu hsize) := by
  intro e
  exact ⟨(binaryShape (a := a) hsize H hin).target e,
    binaryShape_target_embedding hlu hsize H hin e.1 e.2⟩

theorem shape_extractedInner_eq (hlu : l ≤ u) (hsize : shapeM l u = 2)
    (H : BinaryGraph n 3)
    (hin : ∀ e, boundaryAnchoredInfinityCollapses l u (Sum.inl (H.target e))) :
    (shapeNative (a := a) H).extractedInner (m := 1) (slot hlu hsize)
      (shape_innerClosed hlu hsize H hin) = binaryShape (a := a) hsize H hin := by
  apply Graph.ext
  funext ⟨v,j⟩
  apply graftInnerVertex_injective (a := 0) (l := 1) (slot hlu hsize)
  exact ((shapeNative (a := a) H).extractedInnerTarget_spec _ _ _).trans
    (binaryShape_target_embedding hlu hsize H hin v j).symm

theorem coefficient_full_eq_rawShape (hlu : l ≤ u) (hsize : shapeM l u = 2)
    (H : BinaryGraph n 3)
    (hin : ∀ e, boundaryAnchoredInfinityCollapses l u (Sum.inl (H.target e))) :
    coefficient H (slot hlu hsize) Finset.univ =
      rawBinaryWeight (InfinityBoundaryGraphFactorization.shapeN a+1) (binaryShape (a := a) hsize H hin) := by
  rw [coefficient_full_eq_native H _ (shape_count (a := a)) (shapeLabels (a := a))]
  have hd : (shapeNative (a := a) H).CoarseDistinct (l := 1) (slot hlu hsize) := by
    intro v
    exact Fin.elim0 v
  have hf := GraphGeneralWeightedGraft.graftProfile_eq_extractedProduct
    (slot hlu hsize) (rawBinaryWeight 0) (rawBinaryWeight (InfinityBoundaryGraphFactorization.shapeN a+1))
    (shapeNative (a := a) H) (shape_innerClosed hlu hsize H hin) hd
  refine hf.trans ?_
  change 1 * rawBinaryWeight _ ((shapeNative (a := a) H).extractedInner (m := 1) _ _) = _
  rw [one_mul,shape_extractedInner_eq]

theorem coefficient_full_eq_canonicalShapeWeight (hlu : l ≤ u) (hsize : shapeM l u = 2)
    (H : BinaryGraph n 3)
    (hin : ∀ e, boundaryAnchoredInfinityCollapses l u (Sum.inl (H.target e)))
    (hD : ∑ _ : Fin (InfinityBoundaryGraphFactorization.shapeN a+1), 2 =
      GraphForms.dimension (InfinityBoundaryGraphFactorization.shapeN a) (shapeM l u)) :
    coefficient H (slot hlu hsize) Finset.univ =
      GeometricWeights.canonicalWeight (shapeGraph (a := a) H hin) hD := by
  rw [coefficient_full_eq_rawShape (a := a) hlu hsize H hin,
    MainRealGraftPhysicalCoefficient.canonicalWeight_eq_raw_cast hsize]
  rfl

theorem noOutgoing_of_shape_innerClosed (hlu : l ≤ u) (hsize : shapeM l u = 2)
    (H : BinaryGraph n 3)
    (hc : (shapeNative (a := a) H).InnerClosed (l := 1) (slot hlu hsize)) :
    ∀ e, boundaryAnchoredInfinityCollapses l u (Sum.inl (H.target e)) := by
  rintro ⟨v,j⟩
  let sv := InfinityBoundaryGraphCoordinates.sourceEquiv (a := a) v
  have he : shapeLabels (a := a) (Fin.natAdd 0 sv) = v := by
    change InfinityBoundaryGraphCoordinates.sourceEquiv.symm (Fin.cast (Nat.zero_add _) (Fin.natAdd 0 sv)) = v
    have hf : Fin.cast (Nat.zero_add _) (Fin.natAdd 0 sv) = sv := by apply Fin.ext; simp
    rw [hf]
    exact Equiv.symm_apply_apply _ _
  have htgt := Graph.reindexForGraft_target_inner (o := 1) (l := 1) H
    (shapeLabels (a := a)) (Equiv.refl (Fin 3)) sv j
  change (shapeNative (a := a) H).target
      (graftInnerEdge (fun _ : Fin 0 ↦ 2) (fun _ : Fin (InfinityBoundaryGraphFactorization.shapeN a+1) ↦ 2) ⟨sv,j⟩) = _ at htgt
  rw [he] at htgt
  obtain ⟨z,hz⟩ := hc ⟨sv,j⟩
  have ht := hz.trans htgt
  cases hv : H.target ⟨v,j⟩ with
  | inl w => trivial
  | inr w =>
    rw [hv] at ht
    cases z with
    | inl z => cases ht
    | inr z =>
      have hw : graftInnerBoundary (l := 1) (slot hlu hsize) z = w := Sum.inr.inj ht
      change w ∈ boundaryClusterBlock l u
      rw [← hw]
      have hs := shapeM_eq_sub hlu
      have hz := z.isLt
      have hl : l.val ≤ u.val := hlu
      simp only [mem_boundaryClusterBlock,graftInnerBoundary,slot]
      omega

include a in
theorem coefficient_full_of_not_noOutgoing (hlu : l ≤ u) (hsize : shapeM l u = 2)
    (H : BinaryGraph n 3)
    (hin : ¬ ∀ e, boundaryAnchoredInfinityCollapses l u (Sum.inl (H.target e))) :
    coefficient H (slot hlu hsize) Finset.univ = 0 := by
  rw [coefficient_full_eq_native H _ (shape_count (a := a)) (shapeLabels (a := a))]
  apply GraphGeneralWeightedGraft.graftProfile_eq_zero_of_not_admissible
  intro h
  exact hin (noOutgoing_of_shape_innerClosed (a := a) hlu hsize H h.1)

end EnvelopingIsomorphism.Deformation.MainNullaryInfinityCoefficients
