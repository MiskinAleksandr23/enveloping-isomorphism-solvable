import EnvelopingIsomorphism.Deformation.Kontsevich.InfinityBoundaryGraphIntegral
import EnvelopingIsomorphism.Deformation.GeneralGraphReindexing

/-! Geometric weight matching on the surviving all-interior infinity face.
The actual relabelled shape graph and edge order are constructed explicitly. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.InfinityBoundaryGraphMatching
open scoped Classical BigOperators
open BoundaryAnchoredInfinityFreeCoordinates InfinityBoundaryGraphFactorization
open InfinityBoundaryGraphCoordinates InfinityBoundaryGraphIntegral
open KontsevichGraph.General
variable {n m : ℕ} {a : Fin n} {o : Fin m} {l u : Fin (m+1)} {q : Fin n → ℕ}

def pulledArity (q : Fin n → ℕ) : Fin (shapeN a + 1) → ℕ := fun v ↦ q (sourceEquiv.symm v)
def oldEdgeEquiv : KontsevichGraph.General.Edge (pulledArity (a := a) q) ≃ KontsevichGraph.General.Edge q :=
  reindexEdgeEquiv q sourceEquiv.symm

theorem shapeTarget_injective (v w : Fin n ⊕ Fin m)
    (hv : boundaryAnchoredInfinityCollapses l u (Sum.inl v))
    (hw : boundaryAnchoredInfinityCollapses l u (Sum.inl w))
    (he : shapeTarget (a := a) v hv = shapeTarget w hw) : v = w := by
  cases v with
  | inl j =>
    cases w with
    | inl k =>
      apply congrArg Sum.inl
      exact (sourceEquiv (a := a)).injective (Sum.inl.inj he)
    | inr k => cases he
  | inr j =>
    cases w with
    | inl k => cases he
    | inr k =>
      exact congrArg (fun z : BoundaryGraphFaceFactorization.ShapeBoundary l u ↦ Sum.inr z.val)
        ((BoundaryGraphOrderedCoordinates.shapeOrderedEnum l u).injective (Sum.inr.inj he))

variable (Γ : Graph q m)
variable (hin : ∀ e, boundaryAnchoredInfinityCollapses l u (Sum.inl (Γ.target e)))

def shapeGraph : Graph (pulledArity (a := a) q) (shapeM l u) where
  target e := shapeTarget (Γ.target (oldEdgeEquiv e)) (hin _)
  noLoops v j := by
    intro he
    apply Γ.noLoops (sourceEquiv.symm v) j
    have h := shapeTarget_injective (a := a) (Γ.target (oldEdgeEquiv ⟨v,j⟩))
      (Sum.inl (sourceEquiv.symm v)) (hin _) True.intro
    apply h
    change _ = Sum.inl (source (sourceEquiv.symm v))
    change _ = Sum.inl (sourceEquiv (sourceEquiv.symm v))
    rw [Equiv.apply_symm_apply]
    exact he
  distinctTargets v j k he :=
    Γ.distinctTargets (sourceEquiv.symm v) (shapeTarget_injective _ _ (hin _) (hin _) he)

def originalEdges (order : Fin (Degree a l u) ≃ KontsevichGraph.General.Edge q) (j : Fin (Degree a l u)) :
    InfinityBoundaryGraphFactorization.Edge n m := ((order j).1, Γ.target (order j))

def shapeOrder (order : Fin (Degree a l u) ≃ KontsevichGraph.General.Edge q) :
    Fin (Degree a l u) ≃ KontsevichGraph.General.Edge (pulledArity (a := a) q) :=
  order.trans oldEdgeEquiv.symm

theorem shapeEdges_eq (order : Fin (Degree a l u) ≃ KontsevichGraph.General.Edge q) :
    (fun j ↦ shapeEdge (a := a) (originalEdges Γ order j) (hin (order j))) =
      GeometricWeights.orderedEdges (shapeGraph Γ hin) (shapeOrder order) := by
  funext j
  have he : oldEdgeEquiv ((shapeOrder order) j) = order j := by simp [shapeOrder]
  have hs : source (oldEdgeEquiv ((shapeOrder order) j)).1 = ((shapeOrder order) j).1 := by
    change sourceEquiv (sourceEquiv.symm _) = _
    exact sourceEquiv.apply_symm_apply _
  rw [he] at hs
  change GraphForms.Edge.mk (source (order j).1) (shapeTarget (Γ.target (order j)) _) =
    GraphForms.Edge.mk ((shapeOrder order j).1) (shapeTarget (Γ.target (oldEdgeEquiv (shapeOrder order j))) _)
  congr 1
  simp only [he]

variable (ho : o ∉ boundaryClusterBlock l u)
    (hall : ∀ j : Fin m, j ≠ o → j ∈ boundaryClusterBlock l u)

theorem normalized_outwardIntegral_eq_shapeWeight (hlu : l ≤ u)
    (order : Fin (Degree a l u) ≃ KontsevichGraph.General.Edge q) :
    (∏ v : Fin n, ((q v).factorial : ℝ)⁻¹) * ((2 * Real.pi) ^ Degree a l u)⁻¹ *
      outwardIntegral ho hall (originalEdges Γ order) =
      -GeometricWeights.geometricWeight (shapeGraph Γ hin) (shapeOrder order) := by
  rw [outwardIntegral_eq_shape ho hall _ hlu (fun j ↦ hin (order j)), shapeEdges_eq Γ hin order]
  have hf : GeometricWeights.outgoingFactor (pulledArity (a := a) q) =
      ∏ v : Fin n, ((q v).factorial : ℝ)⁻¹ :=
    (sourceEquiv (a := a)).symm.prod_comp (fun v ↦ ((q v).factorial : ℝ)⁻¹)
  simp only [GeometricWeights.geometricWeight, hf, mul_neg]

theorem shapeDegree (order : Fin (Degree a l u) ≃ KontsevichGraph.General.Edge q) :
    ∑ v, pulledArity (a := a) q v = GraphForms.dimension (shapeN a) (shapeM l u) := by
  have h := Fintype.card_congr (shapeOrder order)
  simpa only [KontsevichGraph.General.Edge, Fintype.card_sigma, Fintype.card_fin] using h.symm

/-- The final row-order sign is the literal permutation from the extracted
edge order to the canonical vertex-major order. -/
theorem normalized_outwardIntegral_eq_canonicalShapeWeight (hlu : l ≤ u)
    (order : Fin (Degree a l u) ≃ KontsevichGraph.General.Edge q) :
    (∏ v : Fin n, ((q v).factorial : ℝ)⁻¹) * ((2 * Real.pi) ^ Degree a l u)⁻¹ *
      outwardIntegral ho hall (originalEdges Γ order) =
      -(Equiv.Perm.sign ((shapeOrder order).trans
        (GeometricWeights.canonicalOrder (shapeDegree order)).symm) : ℝ) *
        GeometricWeights.canonicalWeight (shapeGraph Γ hin) (shapeDegree order) := by
  rw [normalized_outwardIntegral_eq_shapeWeight Γ hin ho hall hlu order]
  have he : ((shapeOrder order).trans
      (GeometricWeights.canonicalOrder (shapeDegree order)).symm).trans
      (GeometricWeights.canonicalOrder (shapeDegree order)) = shapeOrder order := by
    apply Equiv.ext
    intro j
    simp
  have h := GeometricWeights.geometricWeight_permute (shapeGraph Γ hin)
    (GeometricWeights.canonicalOrder (shapeDegree order))
    ((shapeOrder order).trans (GeometricWeights.canonicalOrder (shapeDegree order)).symm)
  rw [he] at h
  rw [h]
  simp only [GeometricWeights.canonicalWeight, neg_mul]

/-- Admissibility of the extracted shape is obtained from the literal native
face coefficient; no separate no-outgoing assumption is needed. -/
theorem graph_noOutgoing_of_nonzero
    (order : Fin (Degree a l u) ≃ KontsevichGraph.General.Edge q)
    (x : Fin (Degree a l u) → ℝ) (hx : x ∈ nativeDomain ho hall)
    (hne : BoxStokes.facePullback (radialForm ho hall (originalEdges Γ order))
      0 0 x (BoxStokes.standardBasis _) ≠ 0) :
    ∀ e, boundaryAnchoredInfinityCollapses l u (Sum.inl (Γ.target e)) := by
  have hz := noOutgoing_of_face_ne_zero (originalEdges Γ order)
    ((faceCoordinates ho hall).symm x) hx
    (fun j ↦ (faceCoordinates ho hall).symm (Pi.single j (1 : ℝ)))
    (by rwa [facePullback_eq_native] at hne)
  intro e
  simpa only [originalEdges, Equiv.apply_symm_apply] using hz (order.symm e)

theorem normalized_outwardIntegral_eq_shapeWeight_of_nonzero (hlu : l ≤ u)
    (order : Fin (Degree a l u) ≃ KontsevichGraph.General.Edge q)
    (x : Fin (Degree a l u) → ℝ) (hx : x ∈ nativeDomain ho hall)
    (hne : BoxStokes.facePullback (radialForm ho hall (originalEdges Γ order))
      0 0 x (BoxStokes.standardBasis _) ≠ 0) :
    let hin := graph_noOutgoing_of_nonzero Γ ho hall order x hx hne
    (∏ v : Fin n, ((q v).factorial : ℝ)⁻¹) * ((2 * Real.pi) ^ Degree a l u)⁻¹ *
      outwardIntegral ho hall (originalEdges Γ order) =
      -GeometricWeights.geometricWeight (shapeGraph Γ hin) (shapeOrder order) := by
  exact normalized_outwardIntegral_eq_shapeWeight Γ _ ho hall hlu order

end EnvelopingIsomorphism.Deformation.Kontsevich.InfinityBoundaryGraphMatching
