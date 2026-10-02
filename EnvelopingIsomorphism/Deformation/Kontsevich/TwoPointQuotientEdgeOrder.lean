import EnvelopingIsomorphism.Deformation.Kontsevich.TwoPointQuotientCoarseLabels
import EnvelopingIsomorphism.Deformation.UniformBinaryQuotientEdges

/-! Exact original external-arrow ordering and native coarse relabeling of the
actual curvature quotient extracted from a binary two-point collision. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace EnvelopingIsomorphism.Deformation.Kontsevich.TwoPointQuotientEdgeOrder
open KontsevichGraph.General UniformBinaryGraphs UniformBinaryContraction
open KontsevichGraph.General.TwoVertexContraction
open InteriorGraphFaceCoordinates TwoPointBinaryFaceAdmissibility TwoPointQuotientCoarseLabels
open scoped Classical
variable {n : ℕ} (v : Fin (n + 1)) (H : BinaryGraph (n + 2) 3) (c s : Fin 2)
  (hi : UniqueInternalAt v H c s) (hd : CoarseDistinct v H) (hx : ExitsDistinctAt v H c s)

include hi in
theorem isInternal_iff_slot (e : KontsevichGraph.General.Edge (fun _ : Fin (n + 2) => 2)) :
    IsInternal (cluster v) (e.1, H.target e) ↔ e = ⟨vertexSplitChild v c,s⟩ := by
  constructor
  · rintro ⟨k, ht, hs, hk⟩
    obtain ⟨a,ha⟩ := (mem_cluster v e.1).mp hs
    rcases e with ⟨w,j⟩
    change vertexSplitChild v a = w at ha
    subst w
    have hlocal : vertexSplitCollapseVertex v (localTarget v H ⟨a,j⟩) = Sum.inl v := by
      obtain ⟨b,hb⟩ := (mem_cluster v k).mp hk
      change H.target ⟨vertexSplitChild v a,j⟩ = Sum.inl k at ht
      rw [localTarget, ht, ← hb, vertexSplitCollapseVertex_child]
    exact congrArg (fun e : KontsevichGraph.General.Edge bivectorArity =>
      (⟨vertexSplitChild v e.1,e.2⟩ : KontsevichGraph.General.Edge (fun _ : Fin (n + 2) => 2)))
      ((hi ⟨a,j⟩).mp hlocal)
  · rintro rfl
    obtain ⟨b,hb⟩ := (vertexSplitCollapse_eq_root_iff v _).mp ((hi ⟨c,s⟩).mpr rfl)
    exact ⟨vertexSplitChild v b, hb.symm, child_mem_cluster v c, child_mem_cluster v b⟩

/-- Every quotient slot is exactly one actual noninternal original arrow. -/
def externalEquiv : KontsevichGraph.General.Edge (Arity v) ≃
    {e : KontsevichGraph.General.Edge (fun _ : Fin (n + 2) => 2) // ¬IsInternal (cluster v) (e.1,H.target e)} :=
  (UniformBinaryQuotientEdges.originalExternalEquiv v H c s hi hd hx).trans
    ((Equiv.refl _).subtypeEquiv (fun e => (not_congr (isInternal_iff_slot v H c s hi e)).symm))

@[simp] theorem externalEquiv_val (e : KontsevichGraph.General.Edge (Arity v)) :
    (externalEquiv v H c s hi hd hx e).val = UniformBinaryQuotientEdges.embedding v H c s hi hd hx e := rfl

variable {i a : Fin (n + 2)} (ha : a ∈ cluster v) (hanchor : i ∈ cluster v → a = i)

/-- Relabel an actual quotient edge into the exact native coarse chart labels. -/
def relabelEdge (e : GraphForms.Edge n 3) : GraphForms.Edge (coarseN i a (cluster v)) 3 :=
  ⟨quotientLabelEquiv v ha hanchor e.source, Sum.map (quotientLabelEquiv v ha hanchor) id e.target⟩

theorem coarseTarget_eq_map_collapse (t : Vertex (n + 2) 3) :
    coarseTarget (i := i) (a := a) (S := cluster v) t =
      Sum.map (quotientLabelEquiv v ha hanchor) id (vertexSplitCollapseVertex v t) := by
  rcases t with t | t
  · exact congrArg Sum.inl (coarseLabel_eq_quotientLabel v t)
  · rfl

theorem coarseEdge_embedding (e : KontsevichGraph.General.Edge (Arity v)) :
    coarseEdge (i := i) (a := a) (S := cluster v)
      ((UniformBinaryQuotientEdges.embedding v H c s hi hd hx e).1,
        H.target (UniformBinaryQuotientEdges.embedding v H c s hi hd hx e)) =
      relabelEdge v ha hanchor ⟨e.1, (curvatureGraph v H c s hi hd hx).target e⟩ := by
  unfold coarseEdge relabelEdge
  congr 1
  · rw [coarseLabel_eq_quotientLabel, UniformBinaryQuotientEdges.embedding_source]
    rfl
  · rw [coarseTarget_eq_map_collapse, ← UniformBinaryQuotientEdges.quotient_target]

variable {p q : ℕ}
  (order : Fin (p + q) ≃ KontsevichGraph.General.Edge (fun _ : Fin (n + 2) => 2))
  (hcount : Fintype.card {j // IsInternal (cluster v) (TwoPointBinaryFaceAdmissibility.orderedEdges H order j)} = p)

/-- Quotient ordering induced by the actual internal/external grouping, with
no unrelated arbitrary order replacing the native graph wedge. -/
def quotientOrder : Fin q ≃ KontsevichGraph.General.Edge (Arity v) :=
  ((externalEnum (TwoPointBinaryFaceAdmissibility.orderedEdges H order) hcount).symm.trans
    (order.subtypeEquiv (fun _ => Iff.rfl))).trans (externalEquiv v H c s hi hd hx).symm

theorem embedding_quotientOrder (j : Fin q) :
    UniformBinaryQuotientEdges.embedding v H c s hi hd hx (quotientOrder v H c s hi hd hx order hcount j) =
      order (externalIndex (TwoPointBinaryFaceAdmissibility.orderedEdges H order) hcount j) := by
  rw [← externalEquiv_val]
  change ((externalEquiv v H c s hi hd hx)
    ((externalEquiv v H c s hi hd hx).symm _)).val = _
  rw [Equiv.apply_symm_apply]
  rfl

/-- Exact coarse edge array of the actual face factorization, including its
native edge ordering and native coarse vertex enumeration. -/
theorem coarseEdges_eq_quotient_order (j : Fin q) :
    coarseEdges (i := i) (a := a) (TwoPointBinaryFaceAdmissibility.orderedEdges H order) hcount j =
      relabelEdge v ha hanchor
        ⟨(quotientOrder v H c s hi hd hx order hcount j).1,
          (curvatureGraph v H c s hi hd hx).target (quotientOrder v H c s hi hd hx order hcount j)⟩ := by
  have h := coarseEdge_embedding v H c s hi hd hx ha hanchor (quotientOrder v H c s hi hd hx order hcount j)
  rw [embedding_quotientOrder] at h
  exact h

end EnvelopingIsomorphism.Deformation.Kontsevich.TwoPointQuotientEdgeOrder
