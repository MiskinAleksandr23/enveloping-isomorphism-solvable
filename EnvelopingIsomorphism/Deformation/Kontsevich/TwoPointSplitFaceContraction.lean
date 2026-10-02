import EnvelopingIsomorphism.Deformation.Kontsevich.TwoPointSplitFaceAdmissibility
import EnvelopingIsomorphism.Deformation.Kontsevich.TwoPointQuotientCoarseLabels

/-! A native quotient graph and its exact external-edge enumeration are
constructed from genuine two-point face admissibility for arbitrary arities. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.TwoPointSplitFaceContraction
open KontsevichGraph.General KontsevichGraph.General.Graph
open InteriorGraphFaceCoordinates TwoPointBinaryFaceAdmissibility TwoPointQuotientCoarseLabels
open TwoPointSplitFaceAdmissibility
open scoped Classical
variable {n m p : ℕ} {q : Fin (n + 1) → ℕ} {qLocal : Fin 2 → ℕ}
variable (v : Fin (n + 1)) (hq : q v = p) (H : Graph (vertexSplitArity q qLocal v) m)

/-- These three properties are all proved from the actual nonzero density. -/
structure Data : Prop where
  unique : ∃! e : KontsevichGraph.General.Edge qLocal,
    vertexSplitCollapseVertex v (localTarget v H e) = Sum.inl v
  coarse : H.SplitCoarseDistinct v
  exits : ∀ e f : KontsevichGraph.General.Edge qLocal,
    vertexSplitCollapseVertex v (localTarget v H e) ≠ Sum.inl v →
    vertexSplitCollapseVertex v (localTarget v H f) ≠ Sum.inl v →
    vertexSplitCollapseVertex v (localTarget v H e) =
      vertexSplitCollapseVertex v (localTarget v H f) → e = f

abbrev Exit := {e : KontsevichGraph.General.Edge qLocal //
  vertexSplitCollapseVertex v (localTarget v H e) ≠ Sum.inl v}
variable (hp : Fintype.card (KontsevichGraph.General.Edge qLocal) = p + 1) (D : Data v H)

include hp D in
theorem card_exits : Fintype.card (Exit v H) = p := by
  have hc : Fintype.card {e : KontsevichGraph.General.Edge qLocal //
      vertexSplitCollapseVertex v (localTarget v H e) = Sum.inl v} = 1 := by
    obtain ⟨e,he,hu⟩ := D.unique
    exact Fintype.card_eq_one_iff.mpr ⟨⟨e,he⟩, fun f => Subtype.ext (hu f.val f.property)⟩
  change Fintype.card {e : KontsevichGraph.General.Edge qLocal //
    ¬ vertexSplitCollapseVertex v (localTarget v H e) = Sum.inl v} = p
  rw [Fintype.card_subtype_compl, hc, hp, Nat.add_sub_cancel]

def legEquiv : Fin p ≃ Exit v H := Fintype.equivOfCardEq (by
  rw [Fintype.card_fin, card_exits v H hp D])
def leg (j : Fin p) : KontsevichGraph.General.Edge qLocal := (legEquiv v H hp D j).val

theorem leg_injective : Function.Injective (leg v H hp D) := by
  intro j k he
  exact (legEquiv v H hp D).injective (Subtype.ext he)

theorem legsOutside : H.SplitLegsOutside v (leg v H hp D) := fun j =>
  (legEquiv v H hp D j).property

theorem legsDistinct : H.SplitLegsDistinct v (leg v H hp D) := by
  intro j k he
  exact leg_injective v H hp D (D.exits _ _ (legsOutside v H hp D j) (legsOutside v H hp D k) he)

theorem leg_covers (e : KontsevichGraph.General.Edge qLocal)
    (he : vertexSplitCollapseVertex v (localTarget v H e) ≠ Sum.inl v) :
    ∃ j, leg v H hp D j = e := by
  obtain ⟨j,hj⟩ := (legEquiv v H hp D).surjective ⟨e,he⟩
  exact ⟨j, congrArg Subtype.val hj⟩

theorem legsComplete : H.SplitLegsComplete v (leg v H hp D) := by
  intro e he
  obtain ⟨j,hj⟩ := leg_covers v H hp D e he
  exact ⟨j, congrArg (fun f => H.target (vertexSplitLocalEdge q qLocal v f)) hj⟩

def quotient : Graph q m := H.contractedGraph v hq (leg v H hp D) D.coarse
  (legsOutside v H hp D) (legsDistinct v H hp D)

def template : Graph qLocal p := H.contractedTemplate v hq (leg v H hp D) D.coarse
  (legsOutside v H hp D) (legsDistinct v H hp D) (legsComplete v H hp D)

def choices : (quotient v hq H hp D).VertexSplitChoices v :=
  H.contractedChoices v hq (leg v H hp D) D.coarse (legsOutside v H hp D) (legsDistinct v H hp D)

theorem reconstruct :
    (quotient v hq H hp D).vertexSplit (template v hq H hp D) v hq (choices v hq H hp D) = H :=
  H.vertexSplit_contracted v hq (leg v H hp D) D.coarse
    (legsOutside v H hp D) (legsDistinct v H hp D) (legsComplete v H hp D)

theorem template_leg (j : Fin p) : (template v hq H hp D).target (leg v H hp D j) = Sum.inr j :=
  H.contractedTemplate_target_leg v hq (leg v H hp D) D.coarse
    (legsOutside v H hp D) (legsDistinct v H hp D) (legsComplete v H hp D) j

def embedding : KontsevichGraph.General.Edge q ↪ KontsevichGraph.General.Edge (vertexSplitArity q qLocal v) :=
  (template v hq H hp D).vertexSplitOldEdge (leg v H hp D) (template_leg v hq H hp D) q v hq

@[simp] theorem embedding_outside (e : VertexSplitOutsideEdge q v) :
    embedding v hq H hp D e.val = vertexSplitOutsideEdge q qLocal v e :=
  Graph.vertexSplitOldEdge_outside _ _ _ e

@[simp] theorem embedding_root (j : Fin p) :
    embedding v hq H hp D ⟨v, Fin.cast hq.symm j⟩ = vertexSplitLocalEdge q qLocal v (leg v H hp D j) :=
  Graph.vertexSplitOldEdge_root _ _ _ j

theorem embedding_source (e : KontsevichGraph.General.Edge q) :
    vertexSplitCollapse v (embedding v hq H hp D e).1 = e.1 := by
  obtain ⟨e,rfl⟩ := (vertexSplitOldEdgeEquiv q v hq).symm.surjective e
  rcases e with e | j
  · simp only [vertexSplitOldEdgeEquiv_symm_outside, embedding_outside, vertexSplitOutsideEdge_source]
    exact splitExternalCollapse_embedding v e.val.1
  · simp only [vertexSplitOldEdgeEquiv_symm_root, embedding_root, vertexSplitLocalEdge_source]
    exact Sum.inl.inj (vertexSplitCollapseVertex_child (m := 0) v _)

theorem quotient_target (e : KontsevichGraph.General.Edge q) :
    (quotient v hq H hp D).target e =
      vertexSplitCollapseVertex v (H.target (embedding v hq H hp D e)) := by
  obtain ⟨e,rfl⟩ := (vertexSplitOldEdgeEquiv q v hq).symm.surjective e
  rcases e with e | j
  · rw [vertexSplitOldEdgeEquiv_symm_outside, embedding_outside]
    exact H.contractedTarget_outside v hq (leg v H hp D) e
  · rw [vertexSplitOldEdgeEquiv_symm_root, embedding_root]
    exact H.contractedTarget_root v hq (leg v H hp D) j

/-- The actual quotient slots are precisely the original noninternal arrows. -/
theorem embedding_external (e : KontsevichGraph.General.Edge q) :
    ¬ IsInternal (cluster v) ((embedding v hq H hp D e).1,H.target (embedding v hq H hp D e)) := by
  obtain ⟨e,rfl⟩ := (vertexSplitOldEdgeEquiv q v hq).symm.surjective e
  rcases e with e | j
  · rw [vertexSplitOldEdgeEquiv_symm_outside, embedding_outside]
    rintro ⟨t,ht,hs,hmem⟩
    exact old_not_mem_cluster v e.val.1 e.property hs
  · rw [vertexSplitOldEdgeEquiv_symm_root, embedding_root]
    rintro ⟨t,ht,hs,hmem⟩
    obtain ⟨c,hc⟩ := (mem_cluster v t).mp hmem
    apply legsOutside v H hp D j
    dsimp only at ht
    rw [ht, ← hc, vertexSplitCollapseVertex_child]

theorem embedding_covers (e : KontsevichGraph.General.Edge (vertexSplitArity q qLocal v))
    (he : ¬ IsInternal (cluster v) (e.1,H.target e)) : ∃ f, embedding v hq H hp D f = e := by
  obtain ⟨e,rfl⟩ := (vertexSplitEdgeEquiv q qLocal v).symm.surjective e
  rcases e with e | e
  · exact ⟨e.val, embedding_outside v hq H hp D e⟩
  · have he' : vertexSplitCollapseVertex v (localTarget v H e) ≠ Sum.inl v := by
      intro hh
      obtain ⟨c,hc⟩ := (vertexSplitCollapse_eq_root_iff v _).mp hh
      exact he ⟨vertexSplitChild v c, hc.symm, child_mem_cluster v e.1, child_mem_cluster v c⟩
    obtain ⟨j,hj⟩ := leg_covers v H hp D e he'
    refine ⟨⟨v,Fin.cast hq.symm j⟩, ?_⟩
    rw [embedding_root, hj]
    rfl

def externalEquiv : KontsevichGraph.General.Edge q ≃
    {e : KontsevichGraph.General.Edge (vertexSplitArity q qLocal v) // ¬IsInternal (cluster v) (e.1,H.target e)} :=
  Equiv.ofBijective (fun e => ⟨embedding v hq H hp D e, embedding_external v hq H hp D e⟩)
    ⟨fun _ _ h => (embedding v hq H hp D).injective (congrArg Subtype.val h), by
      intro e
      obtain ⟨f,hf⟩ := embedding_covers v hq H hp D e.val e.property
      exact ⟨f,Subtype.ext hf⟩⟩

variable {i a b : Fin (n + 2)}

theorem ofNonzero
    (order : Fin (shapeDegree a b (cluster v) + coarseDegree i a (cluster v) m) ≃
      KontsevichGraph.General.Edge (vertexSplitArity q qLocal v))
    (ha : a ∈ cluster v) (hb : b ∈ cluster v) (hba : b ≠ a)
    (y : RealProductCoordinates i a b (cluster v) m)
    (hy : y ∈ InteriorFiberAngleSplit.integrationRegion (shapeN a b (cluster v)) ×ˢ
      GeometricWeights.realDomain (coarseN i a (cluster v)) m)
    (h : realFaceDensity (TwoPointSplitFaceAdmissibility.orderedEdges v H order) y ≠ 0) : Data v H := by
  obtain ⟨hu,hc,he⟩ := contractionData_of_density_ne_zero v H order ha hb hba y hy h
  exact ⟨hu,hc,he⟩

end EnvelopingIsomorphism.Deformation.Kontsevich.TwoPointSplitFaceContraction
