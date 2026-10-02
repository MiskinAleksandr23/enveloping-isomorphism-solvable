import EnvelopingIsomorphism.Deformation.MixedRealGraftPhysicalCoefficient

/-! Slot-preserving incidence maps from the original physical graph to its
actual native mixed carrier. Boundary casts preserve every external label. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.MixedRealPhysicalCarrierRelabelling
open Kontsevich KontsevichGraph.General MixedGraphProfileCarrier MixedGraphTargetProfiles
open MixedGraphBlockRelabelling MixedRealGraftPhysicalCoefficient
open BoundaryGraphFaceFactorization BoundaryGraphOrderedCoordinates BoundaryGraphGraftReconstruction
open scoped Classical

variable {n N m : ℕ} {q : Fin n → ℕ}

def reindexRelabelling (G : Graph q m) (e : Fin N ≃ Fin n) :
    SlotRelabelling G (G.reindex e (Equiv.refl _)) where
  vertices := e.symm
  edges := (reindexEdgeEquiv q e).symm
  source f := by
    obtain ⟨⟨v,j⟩,rfl⟩ := (reindexEdgeEquiv q e).surjective f
    simp only [Equiv.symm_apply_apply]
    exact (Equiv.symm_apply_apply e v).symm
  slot f := by
    obtain ⟨⟨v,j⟩,rfl⟩ := (reindexEdgeEquiv q e).surjective f
    exact congrArg (fun t : Edge (fun v ↦ q (e v)) ↦ t.2.val)
      ((reindexEdgeEquiv q e).symm_apply_apply ⟨v,j⟩)
  target f := by
    rw [Graph.reindex_target,Equiv.apply_symm_apply]
    rfl

@[simp] theorem reindexRelabelling_vertices (G : Graph q m) (e : Fin N ≃ Fin n) :
    (reindexRelabelling G e).vertices = e.symm := rfl

@[simp] theorem castProfileRelabelling_vertices (G : Graph q m) {p : Fin n → ℕ} (h : q = p) :
    (Graph.slotRelabelling_castProfile G h).vertices = Equiv.refl _ := by
  subst p
  rfl

def castGraphRelabelling (G : Graph q m) {p : Fin n → ℕ} (h : q = p) :
    SlotRelabelling G (castGraph h rfl G) := by
  subst p
  exact SlotRelabelling.refl G

@[simp] theorem castGraphRelabelling_vertices (G : Graph q m) {p : Fin n → ℕ} (h : q = p) :
    (castGraphRelabelling G h).vertices = Equiv.refl _ := by
  subst p
  rfl

/-- All equal external-count casts of a native ordered graft induce the
same literal boundary labels, while the source equivalence is explicit. -/
def nativeRelabelling {A B O I : ℕ} {p : Fin (A+B) → ℕ}
    (G : Graph q m) (e : Fin (A+B) ≃ Fin n) (eB : Fin (O+I+1) ≃ Fin m)
    (heB : ∀ j, (eB j).val = j.val) (hm : O+I+1 = m)
    (hp : graftArity (pulledOuterArity q e) (pulledInnerArity q e) = p) :
    SlotRelabelling G (castGraph hp hm (G.reindexForGraft e eB)) := by
  subst m
  have he : eB = Equiv.refl _ := by ext j; exact heB j
  subst eB
  exact ((reindexRelabelling G e).trans
    (Graph.slotRelabelling_castProfile _ (graftArity_pulled q e).symm)).trans
      (castGraphRelabelling _ hp)

@[simp] theorem nativeRelabelling_vertices {A B O I : ℕ} {p : Fin (A+B) → ℕ}
    (G : Graph q m) (e : Fin (A+B) ≃ Fin n) (eB : Fin (O+I+1) ≃ Fin m)
    (heB : ∀ j, (eB j).val = j.val) (hm : O+I+1 = m)
    (hp : graftArity (pulledOuterArity q e) (pulledInnerArity q e) = p) :
    (nativeRelabelling G e eB heB hm hp).vertices = e.symm := by
  subst m
  have he : eB = Equiv.refl _ := by ext j; exact heB j
  subst eB
  simp only [nativeRelabelling,SlotRelabelling.trans,castProfileRelabelling_vertices,castGraphRelabelling_vertices,
    reindexRelabelling_vertices]
  rfl

section Actual
variable {d : ℕ} {i a : Fin (d+1)} {S : Finset (Fin (d+1))} {l u : Fin 3}
variable (H : VectorGraph d 2) (ha : a ∈ S) (hi : i ∉ S)

def outputRelabelling (hv : H.vertex ∉ S) (hlt : l < u) (hs : shapeM l u = 2) :
    SlotRelabelling H.graph (outputPhysicalCarrier H ha hi hv hlt hs).graph :=
  (nativeRelabelling H.graph (anchoredPartitionEquiv ha hi) (boundaryCast hlt)
    (fun _ ↦ rfl) (by have hh := outputOutsideM hs; omega)
    (by rw [outputOuterArity H ha hi hv,outputInnerArity H ha hi hv])).trans
    (outputCarrierRelabelling _ _)

@[simp] theorem outputRelabelling_vertices (hv : H.vertex ∉ S) (hlt : l < u) (hs : shapeM l u = 2) :
    (outputRelabelling H ha hi hv hlt hs).vertices =
      (anchoredPartitionEquiv ha hi).symm.trans (outputVertexEquiv (coarseN i S) (shapeN a S+1)) := by
  simp only [outputRelabelling,SlotRelabelling.trans,nativeRelabelling_vertices,
    outputCarrierRelabelling_vertices]

def inputRelabelling (hv : H.vertex ∈ S) (hlt : l < u) (hs : shapeM l u = 1) :
    SlotRelabelling H.graph (inputPhysicalCarrier H ha hi hv hlt hs).graph :=
  (nativeRelabelling H.graph (anchoredPartitionEquiv ha hi) (boundaryCast hlt)
    (fun _ ↦ rfl) (by have hh := inputOutsideM hs; omega)
    (by rw [inputOuterArity H ha hi hv,inputInnerArity H ha hi hv])).trans
    (inputCarrierRelabelling _ _)

@[simp] theorem inputRelabelling_vertices (hv : H.vertex ∈ S) (hlt : l < u) (hs : shapeM l u = 1) :
    (inputRelabelling H ha hi hv hlt hs).vertices =
      (anchoredPartitionEquiv ha hi).symm.trans (inputVertexEquiv (shapeN a S) (coarseN i S+1)) := by
  simp only [inputRelabelling,SlotRelabelling.trans,nativeRelabelling_vertices,
    inputCarrierRelabelling_vertices]

end Actual
end EnvelopingIsomorphism.Deformation.MixedRealPhysicalCarrierRelabelling
