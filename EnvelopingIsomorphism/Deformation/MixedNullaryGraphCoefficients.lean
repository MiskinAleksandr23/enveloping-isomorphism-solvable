import EnvelopingIsomorphism.Deformation.MixedRealPhysicalClusterCoefficients
import EnvelopingIsomorphism.Deformation.MixedRealGraftPhysicalCoefficient
import EnvelopingIsomorphism.Deformation.Kontsevich.PureBoundaryGraphMatching
import EnvelopingIsomorphism.Deformation.Kontsevich.InfinityBoundaryGraphMatching

/-! Exact physical empty-binary-subset coefficients, retaining the marked
vector and the literal extracted quotient or shape graph. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace EnvelopingIsomorphism.Deformation.MixedNullaryGraphCoefficients
open Kontsevich KontsevichGraph.General MixedGraphProfileCarrier MixedGraphTargetProfiles
open MixedRealPhysicalClusterCoefficients MixedRealGraftPhysicalCoefficient
open MixedGraphLabelledClusterCounting GraphLabelledClusterCounting
open MixedGraphBlockRelabelling GraphCanonicalBinaryWeights MixedGraphClusterSums
open scoped Classical
variable {N : ℕ}

def emptyCluster (N : ℕ) : Clusters (binaryBlock N 0) := ⟨∅,by simp⟩

theorem output_coefficient_empty (H : VectorGraph (N+0) 2) :
    rawOutputClusterCoefficient (a := N) (b := 0) H (emptyCluster N) =
      outputProfile (rawVelocityWeight N) (rawBinaryWeight 0) H := by
  let e : ClusterFiber (binaryBlock N 0) (∅ : Finset _) :=
    ⟨Equiv.refl _, by intro j; simp [binaryBlock]⟩
  rw [rawOutputClusterCoefficient_eq H (emptyCluster N) e]
  simp [e, internalGraphEquiv_symm_apply, internalGraphEquiv_refl]

theorem input_coefficient_empty (r : Fin 2) (H : VectorGraph (N+0) 2) :
    rawInputClusterCoefficient (a := N) (b := 0) r H (emptyCluster N) =
      inputProfile r (rawVelocityWeight N) (rawBinaryWeight 0) H := by
  let e : ClusterFiber (binaryBlock N 0) (∅ : Finset _) :=
    ⟨Equiv.refl _, by intro j; simp [binaryBlock]⟩
  rw [rawInputClusterCoefficient_eq r H (emptyCluster N) e]
  simp [e, internalGraphEquiv_symm_apply, internalGraphEquiv_refl]

theorem outputArity_zero (i : Fin (N+1)) :
    graftArity (vectorArity i) (fun _ : Fin 0 ↦ 2) = vectorArity i := by
  funext v
  have he : Fin.castAdd 0 v = v := rfl
  rw [← he, graftArity_outer]
  rfl

def outputNative (H : VectorGraph N 2) :
    Graph (graftArity (vectorArity H.vertex) (fun _ : Fin 0 ↦ 2)) 2 :=
  Graph.castProfileEquiv (outputArity_zero H.vertex).symm 2 H.graph

private theorem ofProfile_cast {n m : ℕ} {q : Fin (n+1) → ℕ}
    (i : Fin (n+1)) (hq : q = vectorArity i) (G : Graph q m) :
    ofProfile i hq G = ⟨i,Graph.castProfileEquiv hq m G⟩ := by
  subst q
  rfl

theorem outputCarrier_native (H : VectorGraph N 2) :
    outputCarrier H.vertex (outputNative H) = H := by
  rcases H with ⟨i,H⟩
  rw [outputCarrier, ofProfile_cast]
  apply congrArg (Sigma.mk i)
  change Graph.castProfileEquiv (outputArity (b := 0) i) 2
    (transportGraph (outputCount N 0) (outputVertexEquiv N 0)
      (Graph.castProfileEquiv (outputArity_zero i).symm 2 H)) = H
  have hp : outputVertexEquiv N 0 = Equiv.refl _ := rfl
  have ht : transportGraph (outputCount N 0) (outputVertexEquiv N 0)
      (Graph.castProfileEquiv (outputArity_zero i).symm 2 H) =
        Graph.castProfileEquiv (outputArity_zero i).symm 2 H := by
    apply Graph.ext
    funext e
    have he : transportEdgeEquiv (graftArity (vectorArity i) (fun _ : Fin 0 ↦ 2))
        (outputVertexEquiv N 0) e = e := rfl
    rw [← he, transportGraph_target, he]
    cases h : (Graph.castProfileEquiv (outputArity_zero i).symm 2 H).target e <;> rfl
  rw [ht]
  exact (Graph.castProfileEquiv (outputArity_zero i).symm 2).symm_apply_apply H

theorem output_innerClosed (H : VectorGraph N 2) :
    (outputNative H).InnerClosed (m := 0) (l := 1) 0 := by
  intro e
  exact Fin.elim0 e.1

/-- Full coefficient of the physical empty subset, including inadmissible
collapsed quotients. The nullary multiplication factor has weight one. -/
theorem output_empty_eq (H : VectorGraph N 2) :
    rawOutputClusterCoefficient (a := N) (b := 0) H (emptyCluster N) =
      if hd : (outputNative H).CoarseDistinct (m := 0) (l := 1) 0 then
        rawVelocityWeight N ⟨H.vertex,(outputNative H).extractedOuter (m := 0) (l := 1) 0 hd⟩ else 0 := by
  rw [output_coefficient_empty]
  conv_lhs => rw [← outputCarrier_native H, outputProfile_carrier]
  by_cases hd : (outputNative H).CoarseDistinct (m := 0) (l := 1) 0
  · rw [GraphGeneralWeightedGraft.graftProfile_eq_extractedProduct _ _ _ _
      (output_innerClosed H) hd, dif_pos hd]
    simp [rawBinaryWeight]
  · rw [GraphGeneralWeightedGraft.graftProfile_eq_zero_of_not_admissible _ _ _ _
      (fun h ↦ hd h.2), dif_neg hd]

private theorem transportGraph_surjective {n M m : ℕ} {q : Fin n → ℕ}
    (h : n = M) (e : Fin n ≃ Fin M) :
    Function.Surjective (transportGraph (q := q) (m := m) h e) := by
  subst M
  exact (Graph.profileGraphEquiv q m e).surjective

theorem exists_inputNative (H : VectorGraph N 2) :
    ∃ G : Graph (graftArity (fun _ : Fin 0 ↦ 2) (vectorArity H.vertex)) 2,
      inputCarrier H.vertex G = H := by
  let C := (Graph.castProfileEquiv (inputArity (b := 0) H.vertex) 2).symm H.graph
  obtain ⟨G,hG⟩ := transportGraph_surjective (inputCount N 0) (inputVertexEquiv N 0) C
  refine ⟨G,?_⟩
  rw [inputCarrier,ofProfile_cast,hG]
  change Sigma.mk H.vertex ((Graph.castProfileEquiv (inputArity (b := 0) H.vertex) 2) C) = H
  rw [Equiv.apply_symm_apply]

def inputNative (H : VectorGraph N 2) :
    Graph (graftArity (fun _ : Fin 0 ↦ 2) (vectorArity H.vertex)) 2 :=
  (exists_inputNative H).choose

theorem inputCarrier_native (H : VectorGraph N 2) :
    inputCarrier H.vertex (inputNative H) = H := (exists_inputNative H).choose_spec

theorem input_coarseDistinct (H : VectorGraph N 2) (r : Fin 2) :
    (inputNative H).CoarseDistinct (m := 1) (l := 0) r := by
  intro v
  exact Fin.elim0 v

/-- Each actual input slot has its genuine retained-vector shape weight
precisely when every edge remains in that shape. -/
theorem input_empty_eq (H : VectorGraph N 2) (r : Fin 2) :
    rawInputClusterCoefficient (a := N) (b := 0) r H (emptyCluster N) =
      if hc : (inputNative H).InnerClosed (m := 1) (l := 0) r then
        rawVelocityWeight N ⟨H.vertex,(inputNative H).extractedInner (m := 1) (l := 0) r hc⟩ else 0 := by
  rw [input_coefficient_empty]
  conv_lhs => rw [← inputCarrier_native H, inputProfile_carrier]
  by_cases hc : (inputNative H).InnerClosed (m := 1) (l := 0) r
  · rw [GraphGeneralWeightedGraft.graftProfile_eq_extractedProduct _ _ _ _
      hc (input_coarseDistinct H r), dif_pos hc]
    simp [rawBinaryWeight]
  · rw [GraphGeneralWeightedGraft.graftProfile_eq_zero_of_not_admissible _ _ _ _
      (fun h ↦ hc h.1), dif_neg hc]

theorem output_outer_target (H : VectorGraph N 2) (e : Edge (vectorArity H.vertex)) :
    (outputNative H).extractedOuterTarget (m := 0) (l := 1) 0 e =
      Sum.map id (fun _ : Fin 2 ↦ (0 : Fin 1)) (H.graph.target e) := by
  rcases e with ⟨v,j⟩
  unfold Graph.extractedOuterTarget outputNative
  rw [graftOuterEdge_mk, Graph.castProfileEquiv_target]
  simp only [Fin.cast_cast]
  change graftCollapse (a := N+1) (b := 0) (m := 0) (l := 1) 0 (H.graph.target ⟨v,j⟩) = _
  cases ht : H.graph.target ⟨v,j⟩ with
  | inl w =>
    change Sum.elim Sum.inl (fun _ ↦ Sum.inr (0 : Fin 1))
      ((finSumFinEquiv : Fin (N+1) ⊕ Fin 0 ≃ Fin ((N+1)+0)).symm w) = Sum.inl w
    have he : (finSumFinEquiv : Fin (N+1) ⊕ Fin 0 ≃ Fin ((N+1)+0)).symm w = Sum.inl w := by
      apply finSumFinEquiv.injective
      simp
    rw [he]
    rfl
  | inr w => exact congrArg (Sum.inr : Fin 1 → Fin (N+1) ⊕ Fin 1) (Subsingleton.elim _ _)

open PureBoundaryGraphMatching

theorem pure_coarseDistinct_iff (H : VectorGraph N 2) :
    (outputNative H).CoarseDistinct (m := 0) (l := 1) 0 ↔
      QuotientDistinct (l := (0 : Fin 3)) (u := 2) (by decide) H.graph := by
  have he : ∀ e, (outputNative H).extractedOuterTarget (m := 0) (l := 1) 0 e =
      quotientTarget (l := (0 : Fin 3)) (u := 2) (by decide) H.graph e := by
    intro e
    rw [output_outer_target]
    unfold quotientTarget
    cases ht : H.graph.target e with
    | inl w => rfl
    | inr w => exact congrArg (Sum.inr : Fin 1 → Fin (N+1) ⊕ Fin 1) (Subsingleton.elim _ _)
  exact forall_congr' fun v ↦ by
    change Function.Injective (fun j ↦ (outputNative H).extractedOuterTarget (m := 0) (l := 1) 0 ⟨v,j⟩) ↔ _
    simp only [he, QuotientDistinct]

/-- Literal quotient graph: collapsing the two physical boundary labels
agrees with the unique nullary output graft extraction, in every edge slot. -/
theorem pure_quotient_eq (H : VectorGraph N 2)
    (hd : QuotientDistinct (l := (0 : Fin 3)) (u := 2) (by decide) H.graph) :
    quotientGraph (l := (0 : Fin 3)) (u := 2) (by decide) H.graph hd =
      (outputNative H).extractedOuter (m := 0) (l := 1) 0 ((pure_coarseDistinct_iff H).mpr hd) := by
  apply Graph.ext
  funext e
  change quotientTarget (l := (0 : Fin 3)) (u := 2) (by decide) H.graph e = (outputNative H).extractedOuterTarget (m := 0) (l := 1) 0 e
  rw [output_outer_target]
  unfold quotientTarget
  cases ht : H.graph.target e with
  | inl w => rfl
  | inr w => exact congrArg (Sum.inr : Fin 1 → Fin (N+1) ⊕ Fin 1) (Subsingleton.elim _ _)

theorem output_empty_eq_quotient (H : VectorGraph N 2) :
    rawOutputClusterCoefficient (a := N) (b := 0) H (emptyCluster N) =
      if hd : QuotientDistinct (l := (0 : Fin 3)) (u := 2) (by decide) H.graph then
        rawVelocityWeight N ⟨H.vertex,quotientGraph (by decide) H.graph hd⟩ else 0 := by
  rw [output_empty_eq]
  by_cases hd : QuotientDistinct (l := (0 : Fin 3)) (u := 2) (by decide) H.graph
  · rw [dif_pos hd, dif_pos ((pure_coarseDistinct_iff H).mpr hd), pure_quotient_eq H hd]
  · rw [dif_neg hd, dif_neg (mt (pure_coarseDistinct_iff H).mp hd)]

private theorem slot_transport {α : Type*} {q : α → ℕ} {x y : α}
    (h : x = y) (j : Fin (q x)) : (h ▸ j).val = j.val := by
  subst y
  rfl

theorem input_native_target (H : VectorGraph N 2) (e : Edge (vectorArity H.vertex)) :
    Sum.map (inputVertexEquiv N 0) id
      ((inputNative H).target (graftInnerEdge (fun _ : Fin 0 ↦ 2) (vectorArity H.vertex) e)) =
      H.graph.target e := by
  have hg := inputCarrier_native H
  rw [inputCarrier,ofProfile_cast] at hg
  have heq : Graph.castProfileEquiv (inputArity (b := 0) H.vertex) 2
      (transportGraph (inputCount N 0) (inputVertexEquiv N 0) (inputNative H)) = H.graph :=
    (Sigma.mk.inj hg).2.eq
  rw [← heq]
  rcases e with ⟨v,j⟩
  rw [Graph.castProfileEquiv_target]
  have he : (⟨v,Fin.cast (congrFun (inputArity (b := 0) H.vertex) v).symm j⟩ :
      Edge (fun v ↦ graftArity (fun _ : Fin 0 ↦ 2) (vectorArity H.vertex)
        ((inputVertexEquiv N 0).symm v))) =
      transportEdgeEquiv _ (inputVertexEquiv N 0)
        (graftInnerEdge (fun _ : Fin 0 ↦ 2) (vectorArity H.vertex) ⟨v,j⟩) := by
    have hs : v = inputVertexEquiv N 0 (Fin.natAdd 0 v) :=
      (inputVertexEquiv_inner (b := 0) v).symm
    apply Sigma.ext hs
    apply (Fin.heq_ext_iff (congrArg _ hs)).mpr
    simp [transportEdgeEquiv, Equiv.sigmaCongrLeft, slot_transport]
  rw [he,transportGraph_target]

def InputClosed (H : VectorGraph N 2) (r : Fin 2) : Prop :=
  ∀ e, ∃ w : Fin (N+1) ⊕ Fin 1, Sum.map id (fun _ : Fin 1 ↦ r) w = H.graph.target e

private theorem input_innerVertex (r : Fin 2) (w : Fin (N+1) ⊕ Fin 1) :
    Sum.map (inputVertexEquiv N 0) id (graftInnerVertex (a := 0) (m := 1) (l := 0) r w) =
      Sum.map id (fun _ : Fin 1 ↦ r) w := by
  cases w with
  | inl v => exact congrArg Sum.inl (inputVertexEquiv_inner (b := 0) v)
  | inr j =>
    apply congrArg Sum.inr
    apply Fin.ext
    simp [graftInnerVertex, graftInnerBoundary, Fin.eq_zero j]

theorem input_closed_iff (H : VectorGraph N 2) (r : Fin 2) :
    (inputNative H).InnerClosed (m := 1) (l := 0) r ↔ InputClosed H r := by
  constructor
  · intro hc e
    obtain ⟨w,hw⟩ := hc e
    refine ⟨w,?_⟩
    rw [← input_innerVertex,hw,input_native_target]
  · intro hc e
    obtain ⟨w,hw⟩ := hc e
    refine ⟨w,?_⟩
    apply (Equiv.sumCongr (inputVertexEquiv N 0) (Equiv.refl (Fin 2))).injective
    change Sum.map (inputVertexEquiv N 0) id _ = Sum.map (inputVertexEquiv N 0) id _
    rw [input_innerVertex,input_native_target,hw]

def inputGraph (H : VectorGraph N 2) (r : Fin 2) (hc : InputClosed H r) :
    Graph (vectorArity H.vertex) 1 :=
  (inputNative H).extractedInner (m := 1) (l := 0) r ((input_closed_iff H r).mpr hc)

theorem inputGraph_target (H : VectorGraph N 2) (r : Fin 2) (hc : InputClosed H r)
    (e : Edge (vectorArity H.vertex)) :
    (inputGraph H r hc).target e =
      Sum.map id (fun _ : Fin 2 ↦ (0 : Fin 1)) (H.graph.target e) := by
  have ht := (inputNative H).extractedInnerTarget_spec (m := 1) (l := 0) r
    ((input_closed_iff H r).mpr hc) e
  have hh := congrArg (Sum.map (inputVertexEquiv N 0) id) ht
  rw [input_innerVertex,input_native_target] at hh
  have he := congrArg (Sum.map id (fun _ : Fin 2 ↦ (0 : Fin 1))) hh
  change _ = _
  rw [← he]
  change _ = Sum.map id (fun _ ↦ (0 : Fin 1))
    (Sum.map id (fun _ : Fin 1 ↦ r) ((inputGraph H r hc).target e))
  cases h : (inputGraph H r hc).target e with
  | inl w => rfl
  | inr j => exact congrArg Sum.inr (Fin.eq_zero j)

theorem input_empty_eq_graph (H : VectorGraph N 2) (r : Fin 2) :
    rawInputClusterCoefficient (a := N) (b := 0) r H (emptyCluster N) =
      if hc : InputClosed H r then rawVelocityWeight N ⟨H.vertex,inputGraph H r hc⟩ else 0 := by
  rw [input_empty_eq]
  by_cases hc : InputClosed H r
  · rw [dif_pos hc,dif_pos ((input_closed_iff H r).mpr hc)]
    rfl
  · rw [dif_neg hc,dif_neg (mt (input_closed_iff H r).mp hc)]

theorem inputClosed_iff_boundary (H : VectorGraph N 2) (r : Fin 2) :
    InputClosed H r ↔ ∀ e j, H.graph.target e = Sum.inr j → j = r := by
  constructor
  · intro hc e j hj
    obtain ⟨w,hw⟩ := hc e
    rw [hj] at hw
    cases w with
    | inl v => cases hw
    | inr k => exact (Sum.inr.inj hw).symm
  · intro hc e
    cases ht : H.graph.target e with
    | inl v => exact ⟨Sum.inl v,rfl⟩
    | inr j =>
      refine ⟨Sum.inr 0,?_⟩
      exact congrArg Sum.inr (hc e j ht).symm

end EnvelopingIsomorphism.Deformation.MixedNullaryGraphCoefficients
