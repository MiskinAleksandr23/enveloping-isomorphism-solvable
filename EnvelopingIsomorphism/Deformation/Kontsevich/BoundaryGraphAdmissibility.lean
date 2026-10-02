import EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryGraphValenceSelection

/-! Necessary graph admissibility conditions derived from the actual nonzero
real-boundary face density. Outgoing edges and parallel quotient edges are
eliminated by genuine form vanishing, not by a graft-extraction assumption. -/

noncomputable section
namespace EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryGraphAdmissibility
open scoped BigOperators Classical
open BoundaryGraphFaceFactorization BoundaryGraphDimensionVanishing BoundaryGraphValenceSelection

variable {n m : ℕ} {i a : Fin n} {S : Finset (Fin n)} {l u : Fin (m + 1)}

theorem nativeFaceDensity_eq_zero_of_outgoing
    (edges : Fin (shapeDegree a S l u + coarseDegree i S l u) → Edge n m)
    (j : Fin (shapeDegree a S l u + coarseDegree i S l u))
    (hloop : (edges j).2 ≠ Sum.inl (edges j).1)
    (hs : (edges j).1 ∈ S)
    (ht : ¬ boundaryClusterCollapses S l u (Sum.inl (edges j).2))
    (y : FaceCoordinates i a S m)
    (hy : (BoundaryClusterFreeCoordinates.faceEmbedding y).OpenConditions l u) :
    nativeFaceDensity (l := l) (u := u) edges y = 0 := by
  have hpoint : faceProductEmbedding (splitFace (l := l) (u := u) y) =
      BoundaryClusterFreeCoordinates.faceEmbedding y := by
    change BoundaryClusterFreeCoordinates.faceEmbedding (splitFace.symm (splitFace y)) = _
    rw [LinearEquiv.symm_apply_apply]
  have hz := graphForm_face_eq_zero_of_outgoing edges j hloop hs ht
    (splitFace (l := l) (u := u) y) (by rwa [hpoint])
  rw [hpoint] at hz
  have hn : (graphForm (l := l) (u := u) edges (BoundaryClusterFreeCoordinates.faceEmbedding y)).compContinuousLinearMap
      BoundaryClusterFreeCoordinates.faceEmbedding = 0 := by
    ext v
    have h := congrArg (fun f ↦ f (fun q ↦ splitFace (l := l) (u := u) (v q))) hz
    change graphForm (l := l) (u := u) edges (BoundaryClusterFreeCoordinates.faceEmbedding y)
      (fun q ↦ faceProductEmbedding (splitFace (l := l) (u := u) (v q))) = 0 at h
    have hv : (fun q ↦ faceProductEmbedding (splitFace (l := l) (u := u) (v q))) =
        fun q ↦ BoundaryClusterFreeCoordinates.faceEmbedding (v q) := by
      funext q
      change BoundaryClusterFreeCoordinates.faceEmbedding (splitFace.symm (splitFace (v q))) = _
      rw [LinearEquiv.symm_apply_apply]
    rw [hv] at h
    exact h
  exact congrArg (fun f ↦ f (fun q ↦ nativeFaceBasis (nativeIndexEnum.symm q))) hn

theorem noOutgoing_of_nativeFaceDensity_ne_zero
    (edges : Fin (shapeDegree a S l u + coarseDegree i S l u) → Edge n m)
    (hloop : ∀ j, (edges j).2 ≠ Sum.inl (edges j).1)
    (y : FaceCoordinates i a S m)
    (hy : (BoundaryClusterFreeCoordinates.faceEmbedding y).OpenConditions l u)
    (hne : nativeFaceDensity (l := l) (u := u) edges y ≠ 0) :
    ∀ j, (edges j).1 ∈ S → boundaryClusterCollapses S l u (Sum.inl (edges j).2) := by
  intro j hj
  by_contra ht
  exact hne (nativeFaceDensity_eq_zero_of_outgoing edges j (hloop j) hj ht y hy)

theorem coarseEdges_injective_of_nativeFaceDensity_ne_zero
    (edges : Fin (shapeDegree a S l u + coarseDegree i S l u) → Edge n m)
    (hc : Fintype.card {j // (edges j).1 ∈ S} = shapeDegree a S l u)
    (hloop : ∀ j, (edges j).2 ≠ Sum.inl (edges j).1)
    (y : FaceCoordinates i a S m)
    (hy : (BoundaryClusterFreeCoordinates.faceEmbedding y).OpenConditions l u)
    (hne : nativeFaceDensity (l := l) (u := u) edges y ≠ 0) :
    Function.Injective (coarseEdges (i := i) (l := l) (u := u) edges S hc) := by
  intro j t he
  by_contra hne'
  exact hne (nativeFaceDensity_eq_zero_of_duplicate_coarse edges hc
    (noOutgoing_of_nativeFaceDensity_ne_zero edges hloop y hy hne) hloop y hy j t hne' he)

variable {q : Fin n → ℕ}

/-- Original clustered graph edges really stay inside the physical collision mask. -/
theorem graph_noOutgoing_of_nativeFaceDensity_ne_zero
    (Γ : KontsevichGraph.General.Graph q m)
    (order : Fin (shapeDegree a S l u + coarseDegree i S l u) ≃ KontsevichGraph.General.Edge q)
    (y : FaceCoordinates i a S m)
    (hy : (BoundaryClusterFreeCoordinates.faceEmbedding y).OpenConditions l u)
    (hne : nativeFaceDensity (l := l) (u := u) (graphEdges Γ order) y ≠ 0) :
    ∀ e : KontsevichGraph.General.Edge q, e.1 ∈ S → boundaryClusterCollapses S l u (Sum.inl (Γ.target e)) := by
  intro e he
  have h := noOutgoing_of_nativeFaceDensity_ne_zero (graphEdges Γ order) (graphEdges_noLoops Γ order)
    y hy hne (order.symm e) (by simpa [graphEdges] using he)
  simpa only [graphEdges, Equiv.apply_symm_apply] using h

/-- Nonzero density forces distinct contracted targets at each original
outside source. This is the real additional condition required for an
admissible outer graph, beyond merely forbidding outgoing cluster edges. -/
theorem graph_coarseTarget_injective_of_nativeFaceDensity_ne_zero
    (Γ : KontsevichGraph.General.Graph q m)
    (order : Fin (shapeDegree a S l u + coarseDegree i S l u) ≃ KontsevichGraph.General.Edge q)
    (y : FaceCoordinates i a S m)
    (hy : (BoundaryClusterFreeCoordinates.faceEmbedding y).OpenConditions l u)
    (hne : nativeFaceDensity (l := l) (u := u) (graphEdges Γ order) y ≠ 0) :
    ∀ v : Fin n, v ∉ S → Function.Injective
      (fun j : Fin (q v) ↦ coarseTarget (i := i) (S := S) (l := l) (u := u) (Γ.target ⟨v, j⟩)) := by
  let edges := graphEdges Γ order
  have hc := internal_count_eq_of_nativeFaceDensity_ne_zero edges (graphEdges_noLoops Γ order) y hy hne
  have hinj := coarseEdges_injective_of_nativeFaceDensity_ne_zero edges hc
    (graphEdges_noLoops Γ order) y hy hne
  intro v hv j t he
  let rj := order.symm ⟨v, j⟩
  let rt := order.symm ⟨v, t⟩
  have hrj : (edges rj).1 ∉ S := by simpa [edges, rj, graphEdges] using hv
  have hrt : (edges rt).1 ∉ S := by simpa [edges, rt, graphEdges] using hv
  let J := externalEnum edges S hc ⟨rj, hrj⟩
  let T := externalEnum edges S hc ⟨rt, hrt⟩
  have hJ : externalIndex edges S hc J = rj := by simp [J, externalIndex]
  have hT : externalIndex edges S hc T = rt := by simp [T, externalIndex]
  have hcoarse : coarseEdges (i := i) (l := l) (u := u) edges S hc J =
      coarseEdges (i := i) (l := l) (u := u) edges S hc T := by
    simp only [coarseEdges, hJ, hT]
    simp only [edges, rj, rt, graphEdges, Equiv.apply_symm_apply]
    change coarseEdge (v, Γ.target ⟨v, j⟩) hv = coarseEdge (v, Γ.target ⟨v, t⟩) hv
    exact congrArg (fun z ↦ (⟨coarseSource v hv, z⟩ : GraphForms.Edge (coarseN i S) (outsideM l u + 1))) he
  have hJT := hinj hcoarse
  have hrows := congrArg (fun z ↦ externalIndex edges S hc z) hJT
  rw [hJ, hT] at hrows
  have hedges := order.symm.injective hrows
  exact Fin.ext (congrArg (fun e : KontsevichGraph.General.Edge q ↦ e.2.val) hedges)

end EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryGraphAdmissibility
