import EnvelopingIsomorphism.Deformation.Kontsevich.TwoPointBinaryFaceAdmissibility
import EnvelopingIsomorphism.Deformation.GeneralGraphVertexSplitExtraction

/-! Nonzero actual two-point face densities force contraction admissibility
for arbitrary outside and child arities, including the retained mixed vector. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.TwoPointSplitFaceAdmissibility
open KontsevichGraph.General KontsevichGraph.General.Graph
open InteriorGraphFaceCoordinates InteriorFaceNonzeroAdmissibility TwoPointBinaryFaceAdmissibility
open scoped Classical
variable {n m d : ℕ} {q : Fin (n + 1) → ℕ} {qLocal : Fin 2 → ℕ}
variable (v : Fin (n + 1)) (H : Graph (vertexSplitArity q qLocal v) m)
  (order : Fin d ≃ KontsevichGraph.General.Edge (vertexSplitArity q qLocal v))

def orderedEdges : Fin d → InteriorGraphFaceCoordinates.Edge (n + 2) m :=
  fun j => ((order j).1, H.target (order j))

def localTarget (e : KontsevichGraph.General.Edge qLocal) : Vertex (n + 2) m :=
  H.target (vertexSplitLocalEdge q qLocal v e)

def localIndex (e : KontsevichGraph.General.Edge qLocal) : Fin d :=
  order.symm (vertexSplitLocalEdge q qLocal v e)

theorem orderedEdges_local (e : KontsevichGraph.General.Edge qLocal) :
    orderedEdges v H order (localIndex v order e) = (vertexSplitChild v e.1, localTarget v H e) := by
  simp only [orderedEdges, localIndex, Equiv.apply_symm_apply, localTarget, vertexSplitLocalEdge_source]

theorem localIndex_injective : Function.Injective (localIndex v order) :=
  order.symm.injective.comp (vertexSplitLocalEdge q qLocal v).injective

theorem local_isInternal_iff (e : KontsevichGraph.General.Edge qLocal) :
    IsInternal (cluster v) (orderedEdges v H order (localIndex v order e)) ↔
      vertexSplitCollapseVertex v (localTarget v H e) = Sum.inl v := by
  rw [orderedEdges_local]
  constructor
  · rintro ⟨j, hj, _, hmem⟩
    obtain ⟨c, rfl⟩ := (mem_cluster v j).mp hmem
    change localTarget v H e = Sum.inl (vertexSplitChild v c) at hj
    rw [hj, vertexSplitCollapseVertex_child]
  · intro h
    obtain ⟨c, hc⟩ := (vertexSplitCollapse_eq_root_iff v _).mp h
    exact ⟨vertexSplitChild v c, hc.symm, child_mem_cluster v e.1, child_mem_cluster v c⟩

/-- An internal original edge necessarily comes from a child slot. -/
theorem internal_has_localIndex (j : Fin d)
    (hj : IsInternal (cluster v) (orderedEdges v H order j)) :
    ∃ e, localIndex v order e = j := by
  obtain ⟨e, he⟩ := (vertexSplitEdgeEquiv q qLocal v).symm.surjective (order j)
  rcases e with e | e
  · have hs := hj.choose_spec.2.1
    change (order j).1 ∈ cluster v at hs
    rw [← he] at hs
    exact (old_not_mem_cluster v e.val.1 e.property hs).elim
  · refine ⟨e, ?_⟩
    apply order.injective
    exact (order.apply_symm_apply _).trans he

/-- Nonzero two-point degree forces exactly one actual child arrow. -/
theorem exists_uniqueInternal_of_count_one
    (hcount : Fintype.card {j // IsInternal (cluster v) (orderedEdges v H order j)} = 1) :
    ∃! e : KontsevichGraph.General.Edge qLocal,
      vertexSplitCollapseVertex v (localTarget v H e) = Sum.inl v := by
  obtain ⟨j, hj⟩ := Fintype.card_eq_one_iff.mp hcount
  obtain ⟨e, he⟩ := internal_has_localIndex v H order j.val j.property
  refine ⟨e, (local_isInternal_iff v H order e).mp (he.symm ▸ j.property), ?_⟩
  intro f hf
  apply localIndex_injective v order
  exact (congrArg Subtype.val (hj ⟨localIndex v order f, (local_isInternal_iff v H order f).mpr hf⟩)).trans he.symm

variable {i a b : Fin (n + 2)} (x : ProductCoordinates i a b (cluster v) m)
  (hx : (toAngular x).toFree.OpenConditions)
  (hnonzero : (graphForm (orderedEdges v H order) (toAngular x)).compContinuousLinearMap
    (fderiv ℝ toAngular x) ≠ 0)
include hx hnonzero

/-- Every unaffected row has distinct collapsed targets; a vector row is
handled by the same proof as all other native arities. -/
theorem coarseDistinct_of_nonzero : H.SplitCoarseDistinct v := by
  intro w hw j k ht
  let E : VertexSplitOutsideEdge q v := ⟨⟨w,j⟩,hw⟩
  let F : VertexSplitOutsideEdge q v := ⟨⟨w,k⟩,hw⟩
  let e : Fin d := order.symm (vertexSplitOutsideEdge q qLocal v E)
  let f : Fin d := order.symm (vertexSplitOutsideEdge q qLocal v F)
  have he : ¬ IsInternal (cluster v) (orderedEdges v H order e) := by
    rintro ⟨t, _, hs, _⟩
    have hs' : vertexSplitOldEmbedding v w ∈ cluster v := by
      simpa only [orderedEdges, e, Equiv.apply_symm_apply, vertexSplitOutsideEdge_source] using hs
    exact old_not_mem_cluster v w hw hs'
  have hf : ¬ IsInternal (cluster v) (orderedEdges v H order f) := by
    rintro ⟨t, _, hs, _⟩
    have hs' : vertexSplitOldEmbedding v w ∈ cluster v := by
      simpa only [orderedEdges, f, Equiv.apply_symm_apply, vertexSplitOutsideEdge_source] using hs
    exact old_not_mem_cluster v w hw hs'
  have hc : coarseEdge (i := i) (a := a) (S := cluster v) (orderedEdges v H order e) =
      coarseEdge (orderedEdges v H order f) := by
    unfold coarseEdge
    congr 1
    · simp only [orderedEdges, e, f, Equiv.apply_symm_apply, vertexSplitOutsideEdge_source]
      rfl
    · simpa only [orderedEdges, e, f, Equiv.apply_symm_apply] using
        coarseTarget_eq_of_collapse_eq (i := i) (a := a) v _ _ ht
  have hh := external_coarseEdge_injective_of_nonzero (orderedEdges v H order) x hx hnonzero
    (a₁ := ⟨e,he⟩) (a₂ := ⟨f,hf⟩) hc
  have hh' := (vertexSplitOutsideEdge q qLocal v).injective
    (order.symm.injective (congrArg Subtype.val hh))
  exact eq_of_heq (Sigma.mk.inj (congrArg Subtype.val hh')).2

/-- All actual exiting child edges have distinct collapsed targets. -/
theorem exitsDistinct_of_nonzero (e f : KontsevichGraph.General.Edge qLocal)
    (he : vertexSplitCollapseVertex v (localTarget v H e) ≠ Sum.inl v)
    (hf : vertexSplitCollapseVertex v (localTarget v H f) ≠ Sum.inl v)
    (ht : vertexSplitCollapseVertex v (localTarget v H e) =
      vertexSplitCollapseVertex v (localTarget v H f)) : e = f := by
  have he' : ¬ IsInternal (cluster v) (orderedEdges v H order (localIndex v order e)) :=
    fun h => he ((local_isInternal_iff v H order e).mp h)
  have hf' : ¬ IsInternal (cluster v) (orderedEdges v H order (localIndex v order f)) :=
    fun h => hf ((local_isInternal_iff v H order f).mp h)
  have hc : coarseEdge (i := i) (a := a) (S := cluster v)
      (orderedEdges v H order (localIndex v order e)) =
      coarseEdge (orderedEdges v H order (localIndex v order f)) := by
    rw [orderedEdges_local, orderedEdges_local]
    unfold coarseEdge
    congr 1
    · exact coarseLabel_child v e.1 f.1
    · exact coarseTarget_eq_of_collapse_eq v _ _ ht
  have hh := external_coarseEdge_injective_of_nonzero (orderedEdges v H order) x hx hnonzero
    (a₁ := ⟨localIndex v order e,he'⟩) (a₂ := ⟨localIndex v order f,hf'⟩) hc
  exact localIndex_injective v order (congrArg Subtype.val hh)

omit hx hnonzero in
/-- All discrete contraction constraints are consequences of a nonzero actual
face density. Neither quotient admissibility nor a factor identity is assumed. -/
theorem contractionData_of_density_ne_zero
    (order : Fin (shapeDegree a b (cluster v) + coarseDegree i a (cluster v) m) ≃
      KontsevichGraph.General.Edge (vertexSplitArity q qLocal v))
    (ha : a ∈ cluster v) (hb : b ∈ cluster v) (hba : b ≠ a)
    (y : RealProductCoordinates i a b (cluster v) m)
    (hy : y ∈ InteriorFiberAngleSplit.integrationRegion (shapeN a b (cluster v)) ×ˢ
      GeometricWeights.realDomain (coarseN i a (cluster v)) m)
    (h : realFaceDensity (orderedEdges v H order) y ≠ 0) :
    (∃! e : KontsevichGraph.General.Edge qLocal,
      vertexSplitCollapseVertex v (localTarget v H e) = Sum.inl v) ∧
    H.SplitCoarseDistinct v ∧
    ∀ e f : KontsevichGraph.General.Edge qLocal,
      vertexSplitCollapseVertex v (localTarget v H e) ≠ Sum.inl v →
      vertexSplitCollapseVertex v (localTarget v H f) ≠ Sum.inl v →
      vertexSplitCollapseVertex v (localTarget v H e) =
        vertexSplitCollapseVertex v (localTarget v H f) → e = f := by
  have hloop : ∀ j, (orderedEdges v H order j).2 ≠ Sum.inl (orderedEdges v H order j).1 :=
    fun j => H.noLoops (order j).1 (order j).2
  have hc := internal_count_eq_one_of_density_ne_zero (orderedEdges v H order) y
    ha hb hba (cluster_card v) hy hloop h
  have hform := form_ne_zero_of_density_ne_zero (orderedEdges v H order) y h
  have hadm := openConditions_toAngular ha hba (toProduct y) hy.1.2 hy.2
  exact ⟨exists_uniqueInternal_of_count_one v H order hc,
    coarseDistinct_of_nonzero v H order (toProduct y) hadm hform,
    exitsDistinct_of_nonzero v H order (toProduct y) hadm hform⟩

end EnvelopingIsomorphism.Deformation.Kontsevich.TwoPointSplitFaceAdmissibility
