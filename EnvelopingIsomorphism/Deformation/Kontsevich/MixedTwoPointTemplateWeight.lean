import EnvelopingIsomorphism.Deformation.Kontsevich.TwoPointSplitCanonicalQuotient
import EnvelopingIsomorphism.Deformation.Kontsevich.MixedTwoPointFaceWeight
import EnvelopingIsomorphism.Deformation.BinaryVertexContraction

/-! Fixed Schouten templates and actual mixed two-point face integrals.
The root-slot comparison is constructed from the genuine template leg map. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.MixedTwoPointTemplateWeight
open KontsevichGraph.General KontsevichGraph.General.Graph
open KontsevichGraph.General.TwoVertexContraction SchoutenGraphContraction
open InteriorGraphFaceCoordinates TwoPointBinaryFaceAdmissibility
open TwoPointSplitFaceContraction TwoPointSplitFaceWeight TwoPointSplitCanonicalQuotient
open MixedGraphCorrectionProfiles MixedGraphPhysicalPairSums GraphCanonicalBinaryWeights
open scoped Classical BigOperators

private theorem target_leg_iff_of_incoming {q : Fin 2 → ℕ} {p : ℕ}
    (Θ : Graph q p) (L : Fin p → KontsevichGraph.General.Edge q)
    (h : ∀ j, Θ.incoming (Sum.inr j) = {L j}) (e : KontsevichGraph.General.Edge q) (j : Fin p) :
    Θ.target e = Sum.inr j ↔ L j = e := by
  have hh := congrArg (fun s => e ∈ s) (h j)
  simpa [Graph.incoming, eq_comm] using hh

theorem vectorForward_leg (e : KontsevichGraph.General.Edge vectorBivectorArity) (j : Fin 2) :
    vectorBivectorForward.target e = Sum.inr j ↔ vectorBivectorForwardLeg j = e :=
  target_leg_iff_of_incoming _ _ vectorBivectorForward_incoming_leg e j

theorem vectorBackward_leg (ρ : Equiv.Perm (Fin 2))
    (e : KontsevichGraph.General.Edge vectorBivectorArity) (j : Fin 2) :
    (vectorBivectorBackward ρ).target e = Sum.inr j ↔ vectorBivectorBackwardLeg ρ j = e :=
  target_leg_iff_of_incoming _ _ (vectorBivectorBackward_incoming_leg ρ) e j

theorem correction_leg (c : Fin 2) (e : KontsevichGraph.General.Edge bivectorArity) (j : Fin 3) :
    (BinaryVertexContraction.canonicalTemplate c).target e = Sum.inr j ↔
      BinaryVertexContraction.canonicalLeg c j = e := by
  rcases e with ⟨a,s⟩
  fin_cases c <;> fin_cases a <;> fin_cases s <;> fin_cases j <;> decide

/-- The three actual source templates, in the order of the Schouten action. -/
def sourceTemplate (c : Fin 3) : Graph vectorBivectorArity 2 :=
  ![vectorBivectorForward, vectorBivectorBackward 1, vectorBivectorBackward (Equiv.swap 0 1)] c

def sourceLeg (c : Fin 3) : Fin 2 → KontsevichGraph.General.Edge vectorBivectorArity :=
  ![vectorBivectorForwardLeg, vectorBivectorBackwardLeg 1,
    vectorBivectorBackwardLeg (Equiv.swap 0 1)] c

theorem source_leg (c : Fin 3) (e : KontsevichGraph.General.Edge vectorBivectorArity) (j : Fin 2) :
    (sourceTemplate c).target e = Sum.inr j ↔ sourceLeg c j = e := by
  fin_cases c
  · exact vectorForward_leg e j
  · exact vectorBackward_leg 1 e j
  · exact vectorBackward_leg (Equiv.swap 0 1) e j

variable {n : ℕ}

theorem source_quotient_weight (Γ : Graph (fun _ : Fin (n + 1) => 2) 2)
    (v : Fin (n + 1)) (c : Fin 3) (χ : Γ.VertexSplitChoices v)
    (D : Data v (Γ.vertexSplit (sourceTemplate c) v rfl χ)) :
    rawBinaryWeight (n + 1)
      (quotient v rfl (Γ.vertexSplit (sourceTemplate c) v rfl χ)
        MixedTwoPointFaceWeight.vectorBivector_edgeCount D) =
    permutationSign (R := ℝ)
      (slotPermutation v rfl Γ (sourceTemplate c) χ (sourceLeg c) (source_leg c)
        MixedTwoPointFaceWeight.vectorBivector_edgeCount D) * rawBinaryWeight (n + 1) Γ :=
  canonicalWeight_quotient v rfl Γ (sourceTemplate c) χ (sourceLeg c) (source_leg c)
    MixedTwoPointFaceWeight.vectorBivector_edgeCount D _

theorem correction_quotient_weight (p : Placement n) (Γ : Graph (twoOddArity p.1 p.2) 2)
    (c : Fin 2) (χ : Γ.VertexSplitChoices p.2)
    (D : Data p.2.val (Γ.vertexSplit (BinaryVertexContraction.canonicalTemplate c)
      p.2.val (selectedArity p).symm χ)) :
    rawCorrectionQuotientWeight ⟨p,
      quotient p.2.val (selectedArity p).symm
        (Γ.vertexSplit (BinaryVertexContraction.canonicalTemplate c) p.2.val (selectedArity p).symm χ)
        MixedTwoPointFaceWeight.bivector_edgeCount D⟩ =
    permutationSign (R := ℝ)
      (slotPermutation p.2.val (selectedArity p).symm Γ (BinaryVertexContraction.canonicalTemplate c)
        χ (BinaryVertexContraction.canonicalLeg c) (correction_leg c)
        MixedTwoPointFaceWeight.bivector_edgeCount D) * rawCorrectionQuotientWeight ⟨p,Γ⟩ :=
  canonicalWeight_quotient p.2.val (selectedArity p).symm Γ (BinaryVertexContraction.canonicalTemplate c)
    χ (BinaryVertexContraction.canonicalLeg c) (correction_leg c)
    MixedTwoPointFaceWeight.bivector_edgeCount D _

section SourceIntegral
variable (Γ : Graph (fun _ : Fin (n + 1) => 2) 2)
    (v : Fin (n + 1)) (c : Fin 3) (χ : Γ.VertexSplitChoices v)
    {i a b : Fin (n + 2)}
    (ha : a ∈ cluster v) (hb : b ∈ cluster v) (hba : b ≠ a)
    (hanchor : i ∈ cluster v → a = i)
    (order : Fin (shapeDegree a b (cluster v) + coarseDegree i a (cluster v) 2) ≃
      KontsevichGraph.General.Edge (vertexSplitArity (fun _ : Fin (n + 1) => 2) vectorBivectorArity v))
    (y : RealProductCoordinates i a b (cluster v) 2)
    (hy : y ∈ InteriorFiberAngleSplit.integrationRegion (shapeN a b (cluster v)) ×ˢ
      GeometricWeights.realDomain (coarseN i a (cluster v)) 2)
    (hne : realFaceDensity (TwoPointSplitFaceAdmissibility.orderedEdges v
      (Γ.vertexSplit (sourceTemplate c) v rfl χ) order) y ≠ 0)

/-- Every actual source template has its original binary quotient weight,
with coefficient one and the two explicit native-to-template ordering signs. -/
theorem normalized_source_template :
    let H := Γ.vertexSplit (sourceTemplate c) v rfl χ
    let D := ofNonzero v H order ha hb hba y hy hne
    let hc := count_of_nonzero v H ha order hb hba y hy hne
    normalizedIntegral v H order =
      faceSign v rfl H MixedTwoPointFaceWeight.vectorBivector_edgeCount D ha hanchor order hc *
      permutationSign (R := ℝ)
        (slotPermutation v rfl Γ (sourceTemplate c) χ (sourceLeg c) (source_leg c)
          MixedTwoPointFaceWeight.vectorBivector_edgeCount D) * rawBinaryWeight (n + 1) Γ := by
  dsimp only
  rw [MixedTwoPointFaceWeight.normalized_source_face_eq_rawBinaryWeight v _ ha hb hba hanchor order y hy hne,
    source_quotient_weight Γ v c χ]
  ring
end SourceIntegral

section CorrectionIntegral
variable (p : Placement n) (Γ : Graph (twoOddArity p.1 p.2) 2)
    (c : Fin 2) (χ : Γ.VertexSplitChoices p.2)
    {i a b : Fin (n + 3)}
    (ha : a ∈ cluster p.2.val) (hb : b ∈ cluster p.2.val) (hba : b ≠ a)
    (hanchor : i ∈ cluster p.2.val → a = i)
    (order : Fin (shapeDegree a b (cluster p.2.val) + coarseDegree i a (cluster p.2.val) 2) ≃
      KontsevichGraph.General.Edge (vertexSplitArity (twoOddArity p.1 p.2) bivectorArity p.2))
    (y : RealProductCoordinates i a b (cluster p.2.val) 2)
    (hy : y ∈ InteriorFiberAngleSplit.integrationRegion (shapeN a b (cluster p.2.val)) ×ˢ
      GeometricWeights.realDomain (coarseN i a (cluster p.2.val)) 2)
    (hne : realFaceDensity (TwoPointSplitFaceAdmissibility.orderedEdges p.2.val
      (Γ.vertexSplit (BinaryVertexContraction.canonicalTemplate c) p.2.val (selectedArity p).symm χ) order) y ≠ 0)

/-- The actual correction coefficient retains the vector placement sign
and the computed factor 3/2 after identifying the original quotient. -/
theorem signed_normalized_correction_template :
    let H := Γ.vertexSplit (BinaryVertexContraction.canonicalTemplate c) p.2.val (selectedArity p).symm χ
    let D := ofNonzero p.2.val H order ha hb hba y hy hne
    let hc := count_of_nonzero p.2.val H ha order hb hba y hy hne
    placementSign p * normalizedIntegral p.2.val H order =
      (3 / 2 : ℝ) * faceSign p.2.val (selectedArity p).symm H
        MixedTwoPointFaceWeight.bivector_edgeCount D ha hanchor order hc *
      permutationSign (R := ℝ)
        (slotPermutation p.2.val (selectedArity p).symm Γ (BinaryVertexContraction.canonicalTemplate c)
          χ (BinaryVertexContraction.canonicalLeg c) (correction_leg c)
          MixedTwoPointFaceWeight.bivector_edgeCount D) *
      (placementSign p * rawCorrectionQuotientWeight ⟨p,Γ⟩) := by
  dsimp only
  rw [MixedTwoPointFaceWeight.signed_normalized_correction_face_eq p _ ha hb hba hanchor order y hy hne,
    correction_quotient_weight p Γ c χ]
  ring
end CorrectionIntegral

end EnvelopingIsomorphism.Deformation.Kontsevich.MixedTwoPointTemplateWeight
