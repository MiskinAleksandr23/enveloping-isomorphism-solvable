import EnvelopingIsomorphism.Deformation.Kontsevich.TwoPointSplitFaceWeight
import EnvelopingIsomorphism.Deformation.MixedGraphOutgoingPairNormalization

/-! Actual mixed two-point face coefficients. Nonzero native density supplies
the quotient graph; its canonical weight has the proved factors one and 3/2. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.MixedTwoPointFaceWeight
open KontsevichGraph.General KontsevichGraph.General.TwoVertexContraction
open InteriorGraphFaceCoordinates TwoPointBinaryFaceAdmissibility
open TwoPointSplitFaceContraction TwoPointSplitFaceWeight
open MixedGraphCorrectionProfiles MixedGraphPhysicalPairSums GraphCanonicalBinaryWeights
open scoped Classical BigOperators
variable {n : ℕ}

theorem vectorBivector_edgeCount : Fintype.card (KontsevichGraph.General.Edge vectorBivectorArity) = 2 + 1 := by
  simp [Fintype.card_sigma, Fin.sum_univ_two, vectorBivectorArity]

theorem bivector_edgeCount : Fintype.card (KontsevichGraph.General.Edge bivectorArity) = 3 + 1 := by
  simp [Fintype.card_sigma, bivectorArity]

private theorem outgoingFactor_ne_zero {N : ℕ} (q : Fin (N + 1) → ℕ) :
    GeometricWeights.outgoingFactor q ≠ 0 := by
  unfold GeometricWeights.outgoingFactor
  apply Finset.prod_ne_zero_iff.mpr
  intro w _
  exact inv_ne_zero (by exact_mod_cast Nat.factorial_ne_zero (q w))

section Source
variable (v : Fin (n + 1))
  (H : Graph (vertexSplitArity (fun _ : Fin (n + 1) => 2) vectorBivectorArity v) 2)
  {i a b : Fin (n + 2)}
  (ha : a ∈ cluster v) (hb : b ∈ cluster v) (hba : b ≠ a)
  (hanchor : i ∈ cluster v → a = i)
  (order : Fin (shapeDegree a b (cluster v) + coarseDegree i a (cluster v) 2) ≃
    KontsevichGraph.General.Edge (vertexSplitArity (fun _ : Fin (n + 1) => 2) vectorBivectorArity v))
  (y : RealProductCoordinates i a b (cluster v) 2)
  (hy : y ∈ InteriorFiberAngleSplit.integrationRegion (shapeN a b (cluster v)) ×ˢ
    GeometricWeights.realDomain (coarseN i a (cluster v)) 2)
  (hne : realFaceDensity (TwoPointSplitFaceAdmissibility.orderedEdges v H order) y ≠ 0)

/-- Actual source face matching: the raw canonical binary quotient weight
and both actual ordering signs, with outgoing ratio exactly one. -/
theorem normalized_source_face_eq_rawBinaryWeight :
    let D := ofNonzero v H order ha hb hba y hy hne
    let hc := count_of_nonzero v H ha order hb hba y hy hne
    normalizedIntegral v H order =
      faceSign v rfl H vectorBivector_edgeCount D ha hanchor order hc *
        rawBinaryWeight (n + 1) (quotient v rfl H vectorBivector_edgeCount D) := by
  have h := normalized_integral_of_nonzero v rfl H vectorBivector_edgeCount
    ha hanchor order hb hba y hy hne
  dsimp only at h ⊢
  rw [VertexSplitOutgoingFactor.vector_bivector_split_factor _ v rfl,
    div_self (outgoingFactor_ne_zero _), one_mul] at h
  exact h

/-- The source quotient and incoming assignment reconstruct the exact
original graph; all its admissibility inputs came from the actual density. -/
theorem source_quotient_reconstruct :
    let D := ofNonzero v H order ha hb hba y hy hne
    (quotient v rfl H vectorBivector_edgeCount D).vertexSplit
      (template v rfl H vectorBivector_edgeCount D) v rfl
      (choices v rfl H vectorBivector_edgeCount D) = H :=
  reconstruct v rfl H vectorBivector_edgeCount _
end Source

section Correction
variable (p : Placement n)
  (H : Graph (vertexSplitArity (twoOddArity p.1 p.2) bivectorArity p.2) 2)
  {i a b : Fin (n + 3)}
  (ha : a ∈ cluster p.2.val) (hb : b ∈ cluster p.2.val) (hba : b ≠ a)
  (hanchor : i ∈ cluster p.2.val → a = i)
  (order : Fin (shapeDegree a b (cluster p.2.val) + coarseDegree i a (cluster p.2.val) 2) ≃
    KontsevichGraph.General.Edge (vertexSplitArity (twoOddArity p.1 p.2) bivectorArity p.2))
  (y : RealProductCoordinates i a b (cluster p.2.val) 2)
  (hy : y ∈ InteriorFiberAngleSplit.integrationRegion (shapeN a b (cluster p.2.val)) ×ˢ
    GeometricWeights.realDomain (coarseN i a (cluster p.2.val)) 2)
  (hne : realFaceDensity (TwoPointSplitFaceAdmissibility.orderedEdges p.2.val H order) y ≠ 0)

/-- Actual curvature correction face with its retained exterior vector.
The coefficient 3/2 is the computed split outgoing-factor ratio. -/
theorem normalized_correction_face_eq_rawQuotientWeight :
    let D := ofNonzero p.2.val H order ha hb hba y hy hne
    let hc := count_of_nonzero p.2.val H ha order hb hba y hy hne
    normalizedIntegral p.2.val H order =
      (3 / 2 : ℝ) * faceSign p.2.val (selectedArity p).symm H bivector_edgeCount D
        ha hanchor order hc *
        rawCorrectionQuotientWeight ⟨p,quotient p.2.val (selectedArity p).symm H bivector_edgeCount D⟩ := by
  have h := normalized_integral_of_nonzero p.2.val (selectedArity p).symm H bivector_edgeCount
    ha hanchor order hb hba y hy hne
  dsimp only at h ⊢
  rw [VertexSplitOutgoingFactor.bivector_split_factor (twoOddArity p.1 p.2) p.2.val (selectedArity p).symm,
    mul_div_cancel_right₀ _ (outgoingFactor_ne_zero _)] at h
  exact h

/-- The genuine two-odd correction sign is retained when the actual
geometric face is assembled with its original odd placements. -/
theorem signed_normalized_correction_face_eq :
    let D := ofNonzero p.2.val H order ha hb hba y hy hne
    let hc := count_of_nonzero p.2.val H ha order hb hba y hy hne
    placementSign p * normalizedIntegral p.2.val H order =
      (3 / 2 : ℝ) * faceSign p.2.val (selectedArity p).symm H bivector_edgeCount D
        ha hanchor order hc *
        (placementSign p * rawCorrectionQuotientWeight
          ⟨p,quotient p.2.val (selectedArity p).symm H bivector_edgeCount D⟩) := by
  dsimp only
  rw [normalized_correction_face_eq_rawQuotientWeight p H ha hb hba hanchor order y hy hne]
  ring

/-- Exact reconstruction of the mixed quotient preserves both odd placements
and every original outside slot, including the vector's one outgoing edge. -/
theorem correction_quotient_reconstruct :
    let D := ofNonzero p.2.val H order ha hb hba y hy hne
    (quotient p.2.val (selectedArity p).symm H bivector_edgeCount D).vertexSplit
      (template p.2.val (selectedArity p).symm H bivector_edgeCount D) p.2.val (selectedArity p).symm
      (choices p.2.val (selectedArity p).symm H bivector_edgeCount D) = H :=
  reconstruct p.2.val (selectedArity p).symm H bivector_edgeCount _
end Correction

end EnvelopingIsomorphism.Deformation.Kontsevich.MixedTwoPointFaceWeight
