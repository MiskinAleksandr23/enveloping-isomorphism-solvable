import EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryGraphDimensionVanishing
import EnvelopingIsomorphism.Deformation.GeneralGraphMixedProfiles

/-! The actual real-boundary face dimension selects the binary and mixed
graft block sizes. Counts are obtained from the original graph's genuine
dependent outgoing edges, not from assumed quotient graphs. -/

noncomputable section
namespace EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryGraphValenceSelection
open scoped BigOperators Classical
open BoundaryGraphFaceFactorization BoundaryGraphDimensionVanishing

variable {n m r : ℕ} {q : Fin n → ℕ}

def graphEdges (Γ : KontsevichGraph.General.Graph q m)
    (order : Fin r ≃ KontsevichGraph.General.Edge q) : Fin r → Edge n m :=
  fun j ↦ ((order j).1, Γ.target (order j))

theorem graphEdges_noLoops (Γ : KontsevichGraph.General.Graph q m)
    (order : Fin r ≃ KontsevichGraph.General.Edge q) :
    ∀ j, (graphEdges Γ order j).2 ≠ Sum.inl (graphEdges Γ order j).1 :=
  fun j ↦ Γ.noLoops (order j).1 (order j).2

/-- The number of actual outgoing edges with clustered source is the sum of
the original vertex arities, retaining the dependent outgoing slot sets. -/
theorem card_source_edges (S : Finset (Fin n)) :
    Fintype.card {e : KontsevichGraph.General.Edge q // e.1 ∈ S} = ∑ v ∈ S, q v := by
  let e : {e : KontsevichGraph.General.Edge q // e.1 ∈ S} ≃
      ((v : ↥S) × Fin (q v.val)) :=
    { toFun e := ⟨⟨e.val.1, e.property⟩, e.val.2⟩
      invFun e := ⟨⟨e.1.val, e.2⟩, e.1.property⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  rw [Fintype.card_congr e, Fintype.card_sigma]
  simp
  exact Finset.sum_attach S q

theorem card_graphEdges_source (Γ : KontsevichGraph.General.Graph q m)
    (order : Fin r ≃ KontsevichGraph.General.Edge q) (S : Finset (Fin n)) :
    Fintype.card {j : Fin r // (graphEdges Γ order j).1 ∈ S} = ∑ v ∈ S, q v := by
  let e : {j : Fin r // (graphEdges Γ order j).1 ∈ S} ≃
      {e : KontsevichGraph.General.Edge q // e.1 ∈ S} :=
    { toFun j := ⟨order j.val, j.property⟩
      invFun e := ⟨order.symm e.val, by simpa [graphEdges] using e.property⟩
      left_inv _ := by simp
      right_inv _ := by simp }
  exact (Fintype.card_congr e).trans (card_source_edges S)

variable {i a : Fin n} {S : Finset (Fin n)} {l u : Fin (m + 1)}

theorem shapeDegree_eq_source_card (ha : a ∈ S) :
    shapeDegree a S l u = 2 * (S.card - 1) + (boundaryClusterBlock l u).card := by
  have he : shapeM l u = (boundaryClusterBlock l u).card :=
    Fintype.card_coe _
  simp only [shapeDegree, GraphForms.dimension, shapeN, card_boundaryClusterShapeIndex _ _ ha, he]
  omega

/-- The genuine nonzero face density forces the valence equation of the
actual cluster, without assuming a graph factorization or graft extraction. -/
theorem valence_eq_of_nativeFaceDensity_ne_zero
    (Γ : KontsevichGraph.General.Graph q m)
    (order : Fin (shapeDegree a S l u + coarseDegree i S l u) ≃ KontsevichGraph.General.Edge q)
    (ha : a ∈ S) (y : FaceCoordinates i a S m)
    (hy : (BoundaryClusterFreeCoordinates.faceEmbedding y).OpenConditions l u)
    (hne : nativeFaceDensity (l := l) (u := u) (graphEdges Γ order) y ≠ 0) :
    ∑ v ∈ S, q v = 2 * (S.card - 1) + (boundaryClusterBlock l u).card := by
  have hc := internal_count_eq_of_nativeFaceDensity_ne_zero (graphEdges Γ order)
    (graphEdges_noLoops Γ order) y hy hne
  rw [card_graphEdges_source, shapeDegree_eq_source_card ha] at hc
  exact hc

/-- Binary clusters meeting the real line have exactly two exterior vertices. -/
theorem binary_block_card_eq_two
    (Γ : KontsevichGraph.General.Graph (fun _ : Fin n ↦ 2) m)
    (order : Fin (shapeDegree a S l u + coarseDegree i S l u) ≃ KontsevichGraph.General.Edge (fun _ : Fin n ↦ 2))
    (ha : a ∈ S) (y : FaceCoordinates i a S m)
    (hy : (BoundaryClusterFreeCoordinates.faceEmbedding y).OpenConditions l u)
    (hne : nativeFaceDensity (l := l) (u := u) (graphEdges Γ order) y ≠ 0) :
    (boundaryClusterBlock l u).card = 2 := by
  have hc := valence_eq_of_nativeFaceDensity_ne_zero Γ order ha y hy hne
  simp at hc
  have hS : 0 < S.card := Finset.card_pos.mpr ⟨a, ha⟩
  omega

theorem sum_single_vector_arity (S : Finset (Fin n)) (x : Fin n) :
    (∑ v ∈ S, KontsevichGraph.General.oneExceptionalArity 1 x v) =
      if x ∈ S then 2 * S.card - 1 else 2 * S.card := by
  by_cases hx : x ∈ S
  · rw [if_pos hx, ← Finset.sum_erase_add S _ hx]
    have he : (∑ v ∈ S.erase x, KontsevichGraph.General.oneExceptionalArity 1 x v) =
        (S.erase x).card * 2 := by
      have hv (v : Fin n) (hv : v ∈ S.erase x) :
          KontsevichGraph.General.oneExceptionalArity 1 x v = 2 :=
        KontsevichGraph.General.oneExceptionalArity_other 1 x v (Finset.mem_erase.mp hv).1
      rw [Finset.sum_congr rfl hv]
      simp
    rw [he, Finset.card_erase_of_mem hx]
    simp only [KontsevichGraph.General.oneExceptionalArity_root]
    have hS : 0 < S.card := Finset.card_pos.mpr ⟨x, hx⟩
    omega
  · rw [if_neg hx]
    have hv (v : Fin n) (hv : v ∈ S) : KontsevichGraph.General.oneExceptionalArity 1 x v = 2 :=
      KontsevichGraph.General.oneExceptionalArity_other 1 x v (fun he ↦ hx (he ▸ hv))
    rw [Finset.sum_congr rfl hv]
    simp [mul_comm]

/-- A mixed cluster has one exterior vertex precisely when its vector lies
inside; if the vector lies outside, the clustered binary valence forces two. -/
theorem mixed_block_card_eq
    (x : Fin n) (Γ : KontsevichGraph.General.Graph (KontsevichGraph.General.oneExceptionalArity 1 x) m)
    (order : Fin (shapeDegree a S l u + coarseDegree i S l u) ≃
      KontsevichGraph.General.Edge (KontsevichGraph.General.oneExceptionalArity 1 x))
    (ha : a ∈ S) (y : FaceCoordinates i a S m)
    (hy : (BoundaryClusterFreeCoordinates.faceEmbedding y).OpenConditions l u)
    (hne : nativeFaceDensity (l := l) (u := u) (graphEdges Γ order) y ≠ 0) :
    (boundaryClusterBlock l u).card = if x ∈ S then 1 else 2 := by
  have hc := valence_eq_of_nativeFaceDensity_ne_zero Γ order ha y hy hne
  rw [sum_single_vector_arity] at hc
  have hS : 0 < S.card := Finset.card_pos.mpr ⟨a, ha⟩
  split_ifs at hc ⊢ <;> omega

theorem block_strict_of_card_pos (hT : 0 < (boundaryClusterBlock l u).card) : l < u := by
  obtain ⟨j, hj⟩ := Finset.card_pos.mp hT
  have hb := (mem_boundaryClusterBlock l u j).mp hj
  change l.val < u.val
  omega

/-- The wrong external block size gives zero actual binary boundary density. -/
theorem binary_density_zero_of_block_card_ne
    (Γ : KontsevichGraph.General.Graph (fun _ : Fin n ↦ 2) m)
    (order : Fin (shapeDegree a S l u + coarseDegree i S l u) ≃ KontsevichGraph.General.Edge (fun _ : Fin n ↦ 2))
    (ha : a ∈ S) (y : FaceCoordinates i a S m)
    (hy : (BoundaryClusterFreeCoordinates.faceEmbedding y).OpenConditions l u)
    (hT : (boundaryClusterBlock l u).card ≠ 2) :
    nativeFaceDensity (l := l) (u := u) (graphEdges Γ order) y = 0 := by
  by_contra hn
  exact hT (binary_block_card_eq_two Γ order ha y hy hn)

/-- The wrong mixed block size gives zero density, including empty blocks. -/
theorem mixed_density_zero_of_block_card_ne
    (x : Fin n) (Γ : KontsevichGraph.General.Graph (KontsevichGraph.General.oneExceptionalArity 1 x) m)
    (order : Fin (shapeDegree a S l u + coarseDegree i S l u) ≃
      KontsevichGraph.General.Edge (KontsevichGraph.General.oneExceptionalArity 1 x))
    (ha : a ∈ S) (y : FaceCoordinates i a S m)
    (hy : (BoundaryClusterFreeCoordinates.faceEmbedding y).OpenConditions l u)
    (hT : (boundaryClusterBlock l u).card ≠ if x ∈ S then 1 else 2) :
    nativeFaceDensity (l := l) (u := u) (graphEdges Γ order) y = 0 := by
  by_contra hn
  exact hT (mixed_block_card_eq x Γ order ha y hy hn)

end EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryGraphValenceSelection
