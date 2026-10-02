import EnvelopingIsomorphism.Deformation.Kontsevich.InteriorFaceNonzeroAdmissibility
import EnvelopingIsomorphism.Deformation.UniformBinaryContraction

/-! Actual two-point graph densities discharge the target-distinctness inputs
of native binary vertex contraction. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace EnvelopingIsomorphism.Deformation.Kontsevich.TwoPointBinaryFaceAdmissibility
open KontsevichGraph.General UniformBinaryGraphs UniformBinaryContraction
open InteriorGraphFaceCoordinates InteriorFaceNonzeroAdmissibility
open scoped Classical
variable {n m d : ℕ} (v : Fin (n + 1))

def cluster : Finset (Fin (n + 2)) := Finset.univ.image (vertexSplitChild v)

@[simp] theorem mem_cluster (j : Fin (n + 2)) :
    j ∈ cluster v ↔ ∃ c : Fin 2, vertexSplitChild v c = j := by simp [cluster]

@[simp] theorem child_mem_cluster (c : Fin 2) : vertexSplitChild v c ∈ cluster v :=
  (mem_cluster v _).mpr ⟨c, rfl⟩

theorem cluster_card : (cluster v).card = 2 := by
  rw [cluster, Finset.card_image_of_injective _ (vertexSplitChild_injective v)]
  simp

theorem old_not_mem_cluster (w : Fin (n + 1)) (hw : w ≠ v) :
    vertexSplitOldEmbedding v w ∉ cluster v := by
  rintro h
  obtain ⟨c, hc⟩ := (mem_cluster v _).mp h
  exact vertexSplitOld_ne_child v w hw c hc.symm

variable {i a : Fin (n + 2)}

theorem coarseLabel_child (c e : Fin 2) :
    coarseLabel (i := i) (a := a) (S := cluster v) (vertexSplitChild v c) =
      coarseLabel (vertexSplitChild v e) := by
  simp only [coarseLabel, ClusterFreeCoordinates.representative, child_mem_cluster, if_true]

/-- Native coarse target equality follows from literal vertex-collapse
equality, independently of any quotient graph or its admissibility. -/
theorem coarseTarget_eq_of_collapse_eq (s t : Vertex (n + 2) m)
    (h : vertexSplitCollapseVertex v s = vertexSplitCollapseVertex v t) :
    coarseTarget (i := i) (a := a) (S := cluster v) s = coarseTarget t := by
  by_cases hs : vertexSplitCollapseVertex v s = Sum.inl v
  · have ht : vertexSplitCollapseVertex v t = Sum.inl v := h.symm.trans hs
    obtain ⟨c, rfl⟩ := (vertexSplitCollapse_eq_root_iff v s).mp hs
    obtain ⟨e, rfl⟩ := (vertexSplitCollapse_eq_root_iff v t).mp ht
    exact congrArg Sum.inl (coarseLabel_child (i := i) (a := a) v c e)
  · have ht : vertexSplitCollapseVertex v t ≠ Sum.inl v := fun ht => hs (h.trans ht)
    have he : s = t := (vertexSplitOldVertex_collapse v s hs).symm.trans
      ((congrArg (vertexSplitOldVertex v) h).trans (vertexSplitOldVertex_collapse v t ht))
    exact congrArg coarseTarget he

variable (H : BinaryGraph (n + 2) 3)
  (order : Fin d ≃ KontsevichGraph.General.Edge (fun _ : Fin (n + 2) => 2))

def orderedEdges : Fin d → InteriorGraphFaceCoordinates.Edge (n + 2) 3 :=
  fun q => ((order q).1, H.target (order q))

def localIndex (e : KontsevichGraph.General.Edge KontsevichGraph.General.TwoVertexContraction.bivectorArity) : Fin d :=
  order.symm ⟨vertexSplitChild v e.1, e.2⟩

theorem orderedEdges_local (e : KontsevichGraph.General.Edge KontsevichGraph.General.TwoVertexContraction.bivectorArity) :
    orderedEdges H order (localIndex v order e) = (vertexSplitChild v e.1, localTarget v H e) := by
  simp [orderedEdges, localIndex, localTarget]

theorem localIndex_injective : Function.Injective (localIndex v order) := by
  rintro ⟨c,s⟩ ⟨e,t⟩ h
  have he := order.symm.injective h
  have hc := vertexSplitChild_injective v (congrArg Sigma.fst he)
  change c = e at hc
  subst e
  have ht : s = t := eq_of_heq (Sigma.mk.inj he).2
  subst t
  rfl

theorem local_isInternal_iff (e : KontsevichGraph.General.Edge KontsevichGraph.General.TwoVertexContraction.bivectorArity) :
    IsInternal (cluster v) (orderedEdges H order (localIndex v order e)) ↔
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

/-- The sole globally internal arrow is an actual unique local binary slot. -/
theorem exists_uniqueInternal_of_count_one
    (hcount : Fintype.card {q // IsInternal (cluster v) (orderedEdges H order q)} = 1) :
    ∃! e : KontsevichGraph.General.Edge KontsevichGraph.General.TwoVertexContraction.bivectorArity,
      vertexSplitCollapseVertex v (localTarget v H e) = Sum.inl v := by
  obtain ⟨q, hq⟩ := Fintype.card_eq_one_iff.mp hcount
  obtain ⟨k, ht, hs, hk⟩ := q.property
  change (order q.val).1 ∈ cluster v at hs
  obtain ⟨c, hc⟩ := (mem_cluster v _).mp hs
  let e : KontsevichGraph.General.Edge KontsevichGraph.General.TwoVertexContraction.bivectorArity :=
    ⟨c, (order q.val).2⟩
  have he : localIndex v order e = q.val := by
    apply order.injective
    simp only [localIndex, Equiv.apply_symm_apply]
    exact Sigma.ext hc (by rfl)
  refine ⟨e, (local_isInternal_iff v H order e).mp (he.symm ▸ q.property), ?_⟩
  intro f hf
  have hh := congrArg Subtype.val (hq ⟨localIndex v order f, (local_isInternal_iff v H order f).mpr hf⟩)
  apply localIndex_injective v order
  exact hh.trans he.symm

variable {b : Fin (n + 2)}
  (x : ProductCoordinates i a b (cluster v) 3)
  (hx : (toAngular x).toFree.OpenConditions)
  (hnonzero : (graphForm (orderedEdges H order) (toAngular x)).compContinuousLinearMap
    (fderiv ℝ toAngular x) ≠ 0)

include hx hnonzero

/-- Outside binary vertices retain distinct actual collapsed targets, since
a duplicate creates two identical native coarse covectors. -/
theorem coarseDistinct_of_nonzero : CoarseDistinct v H := by
  intro w hw j k htarget
  let e : Fin d := order.symm ⟨vertexSplitOldEmbedding v w,j⟩
  let f : Fin d := order.symm ⟨vertexSplitOldEmbedding v w,k⟩
  have he : ¬ IsInternal (cluster v) (orderedEdges H order e) := by
    rintro ⟨t, _, hs, _⟩
    have hs' : vertexSplitOldEmbedding v w ∈ cluster v := by simpa [orderedEdges, e] using hs
    exact old_not_mem_cluster v w hw hs'
  have hf : ¬ IsInternal (cluster v) (orderedEdges H order f) := by
    rintro ⟨t, _, hs, _⟩
    have hs' : vertexSplitOldEmbedding v w ∈ cluster v := by simpa [orderedEdges, f] using hs
    exact old_not_mem_cluster v w hw hs'
  have hc : coarseEdge (i := i) (a := a) (S := cluster v) (orderedEdges H order e) =
      coarseEdge (orderedEdges H order f) := by
    unfold coarseEdge
    congr 1
    · simp [orderedEdges, e, f]
    · simpa [orderedEdges, coarseEdge, e, f] using
        coarseTarget_eq_of_collapse_eq (i := i) (a := a) v _ _ htarget
  have hh := external_coarseEdge_injective_of_nonzero (orderedEdges H order) x hx hnonzero
    (a₁ := ⟨e,he⟩) (a₂ := ⟨f,hf⟩) hc
  have hs : (⟨vertexSplitOldEmbedding v w,j⟩ : KontsevichGraph.General.Edge (fun _ : Fin (n + 2) => 2)) =
      ⟨vertexSplitOldEmbedding v w,k⟩ := order.symm.injective (congrArg Subtype.val hh)
  exact eq_of_heq (Sigma.mk.inj hs).2

/-- The three exiting child arrows also have distinct contracted targets;
their sources coincide in the actual coarse chart. -/
theorem exitsDistinct_of_nonzero (c s : Fin 2) (hi : UniqueInternalAt v H c s) :
    ExitsDistinctAt v H c s := by
  intro e f he hf ht
  have he' : ¬ IsInternal (cluster v) (orderedEdges H order (localIndex v order e)) :=
    fun h => he ((hi e).mp ((local_isInternal_iff v H order e).mp h))
  have hf' : ¬ IsInternal (cluster v) (orderedEdges H order (localIndex v order f)) :=
    fun h => hf ((hi f).mp ((local_isInternal_iff v H order f).mp h))
  have hc : coarseEdge (i := i) (a := a) (S := cluster v)
      (orderedEdges H order (localIndex v order e)) =
      coarseEdge (orderedEdges H order (localIndex v order f)) := by
    rw [orderedEdges_local, orderedEdges_local]
    unfold coarseEdge
    congr 1
    · exact coarseLabel_child v e.1 f.1
    · exact coarseTarget_eq_of_collapse_eq v _ _ ht
  have hh := external_coarseEdge_injective_of_nonzero (orderedEdges H order) x hx hnonzero
    (a₁ := ⟨localIndex v order e,he'⟩) (a₂ := ⟨localIndex v order f,hf'⟩) hc
  exact localIndex_injective v order (congrArg Subtype.val hh)

omit hx hnonzero in
/-- All discrete admissibility inputs for actual binary contraction are
consequences of one nonzero literal simple-face density. -/
theorem exists_contractionData_of_density_ne_zero
    (order : Fin (shapeDegree a b (cluster v) + coarseDegree i a (cluster v) 3) ≃
      KontsevichGraph.General.Edge (fun _ : Fin (n + 2) => 2))
    (ha : a ∈ cluster v) (hb : b ∈ cluster v) (hba : b ≠ a)
    (y : RealProductCoordinates i a b (cluster v) 3)
    (hy : y ∈ InteriorFiberAngleSplit.integrationRegion (shapeN a b (cluster v)) ×ˢ
      GeometricWeights.realDomain (coarseN i a (cluster v)) 3)
    (h : realFaceDensity (orderedEdges H order) y ≠ 0) :
    ∃ c s : Fin 2, UniqueInternalAt v H c s ∧ CoarseDistinct v H ∧ ExitsDistinctAt v H c s := by
  have hloop : ∀ q, (orderedEdges H order q).2 ≠ Sum.inl (orderedEdges H order q).1 :=
    fun q => H.noLoops (order q).1 (order q).2
  have hc := internal_count_eq_one_of_density_ne_zero (orderedEdges H order) y
    ha hb hba (cluster_card v) hy hloop h
  obtain ⟨⟨c,s⟩, he, hu⟩ := exists_uniqueInternal_of_count_one v H order hc
  have hi : UniqueInternalAt v H c s := by
    intro e
    exact ⟨fun h => hu e h, fun h => h ▸ he⟩
  have hform := form_ne_zero_of_density_ne_zero (orderedEdges H order) y h
  have hadm := openConditions_toAngular ha hba (toProduct y) hy.1.2 hy.2
  exact ⟨c, s, hi, coarseDistinct_of_nonzero v H order (toProduct y) hadm hform,
    exitsDistinct_of_nonzero v H order (toProduct y) hadm hform c s hi⟩

end EnvelopingIsomorphism.Deformation.Kontsevich.TwoPointBinaryFaceAdmissibility
