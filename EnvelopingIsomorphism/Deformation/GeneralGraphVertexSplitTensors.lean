import EnvelopingIsomorphism.Deformation.GeneralGraphVertexSplitConstruction

/-! Actual tensor families for the two-child vertex replacement. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.KontsevichGraph.General

variable {n d : ℕ} {R : Type*} [CommRing R]
variable (q : Fin (n + 1) → ℕ) (qLocal : Fin 2 → ℕ) (r : Fin (n + 1))

theorem vertexSplitOutsideEdge_mk (v : Fin (n + 1)) (hv : v ≠ r) (j : Fin (q v)) :
    vertexSplitOutsideEdge q qLocal r ⟨⟨v, j⟩, hv⟩ =
      ⟨vertexSplitOldEmbedding r v, Fin.cast (vertexSplitArity_old q qLocal r v hv).symm j⟩ := by
  apply Sigma.ext (vertexSplitOutsideEdge_source q qLocal r ⟨⟨v, j⟩, hv⟩)
  apply heq_of_eq
  apply Fin.ext
  exact vertexSplitOutsideEdge_slot_val q qLocal r ⟨⟨v, j⟩, hv⟩

theorem vertexSplitLocalEdge_mk (c : Fin 2) (j : Fin (qLocal c)) :
    vertexSplitLocalEdge q qLocal r ⟨c, j⟩ =
      ⟨vertexSplitChild r c, Fin.cast (vertexSplitArity_child q qLocal r c).symm j⟩ := by
  apply Sigma.ext (vertexSplitLocalEdge_source q qLocal r ⟨c, j⟩)
  apply heq_of_eq
  apply Fin.ext
  exact vertexSplitLocalEdge_slot_val q qLocal r ⟨c, j⟩

/-- Old and local coefficient tensors on the canonical source partition. -/
def vertexSplitSourceTensors (T : (v : Fin (n + 1)) → Tensor (q v) d R)
    (TLocal : (c : Fin 2) → Tensor (qLocal c) d R) :
    (s : {v : Fin (n + 1) // v ≠ r} ⊕ Fin 2) →
      Tensor (Sum.elim (fun w : {w : Fin (n + 1) // w ≠ r} ↦ q w.val) qLocal s) d R :=
  Sum.rec
    (motive := fun s : {v : Fin (n + 1) // v ≠ r} ⊕ Fin 2 ↦
      Tensor (Sum.elim (fun w : {w : Fin (n + 1) // w ≠ r} ↦ q w.val) qLocal s) d R)
    (fun w ↦ T w.val) TLocal

/-- The actual coefficient tensor family after replacing the old source by two children. -/
def vertexSplitTensors (T : (v : Fin (n + 1)) → Tensor (q v) d R)
    (TLocal : (c : Fin 2) → Tensor (qLocal c) d R) :
    (v : Fin (n + 2)) → Tensor (vertexSplitArity q qLocal r v) d R :=
  fun v ↦ vertexSplitSourceTensors q qLocal r T TLocal (vertexSplitSourceEquiv r v)

theorem vertexSplitTensors_old_heq (T : (v : Fin (n + 1)) → Tensor (q v) d R)
    (TLocal : (c : Fin 2) → Tensor (qLocal c) d R) (v : Fin (n + 1)) (hv : v ≠ r) :
    HEq (vertexSplitTensors q qLocal r T TLocal (vertexSplitOldEmbedding r v)) (T v) := by
  exact congr_arg_heq (vertexSplitSourceTensors q qLocal r T TLocal)
    (vertexSplitSourceEquiv_old r v hv)

theorem vertexSplitTensors_child_heq (T : (v : Fin (n + 1)) → Tensor (q v) d R)
    (TLocal : (c : Fin 2) → Tensor (qLocal c) d R) (c : Fin 2) :
    HEq (vertexSplitTensors q qLocal r T TLocal (vertexSplitChild r c)) (TLocal c) := by
  exact congr_arg_heq (vertexSplitSourceTensors q qLocal r T TLocal)
    (vertexSplitSourceEquiv_child r c)

/-- Outside coefficient evaluations retain all their original ordered slots. -/
@[simp] theorem vertexSplitTensors_old_labels (T : (v : Fin (n + 1)) → Tensor (q v) d R)
    (TLocal : (c : Fin 2) → Tensor (qLocal c) d R) (v : Fin (n + 1)) (hv : v ≠ r)
    (lab : Edge (vertexSplitArity q qLocal r) → Fin d) :
    vertexSplitTensors q qLocal r T TLocal (vertexSplitOldEmbedding r v)
        (fun j ↦ lab ⟨vertexSplitOldEmbedding r v, j⟩) =
      T v (fun j ↦ lab (vertexSplitOutsideEdge q qLocal r ⟨⟨v, j⟩, hv⟩)) := by
  apply congr_heq (vertexSplitTensors_old_heq q qLocal r T TLocal v hv)
  apply (Fin.heq_fun_iff (vertexSplitArity_old q qLocal r v hv)).mpr
  intro j
  rw [vertexSplitOutsideEdge_mk]
  rfl

/-- Child coefficient evaluations use exactly the original ordered template slots. -/
@[simp] theorem vertexSplitTensors_child_labels (T : (v : Fin (n + 1)) → Tensor (q v) d R)
    (TLocal : (c : Fin 2) → Tensor (qLocal c) d R) (c : Fin 2)
    (lab : Edge (vertexSplitArity q qLocal r) → Fin d) :
    vertexSplitTensors q qLocal r T TLocal (vertexSplitChild r c)
        (fun j ↦ lab ⟨vertexSplitChild r c, j⟩) =
      TLocal c (fun j ↦ lab (vertexSplitLocalEdge q qLocal r ⟨c, j⟩)) := by
  apply congr_heq (vertexSplitTensors_child_heq q qLocal r T TLocal c)
  apply (Fin.heq_fun_iff (vertexSplitArity_child q qLocal r c)).mpr
  intro j
  rw [vertexSplitLocalEdge_mk]
  rfl


end EnvelopingIsomorphism.Deformation.KontsevichGraph.General
