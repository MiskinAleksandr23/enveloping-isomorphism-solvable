import EnvelopingIsomorphism.Deformation.Kontsevich.MixedSourceFaceSign
import EnvelopingIsomorphism.Deformation.Kontsevich.TwoPointTemplateAdmissibility

/-! Unconditional actual integrals of the three mixed source templates. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.MixedSourceTemplateIntegral
open KontsevichGraph.General KontsevichGraph.General.Graph
open KontsevichGraph.General.TwoVertexContraction
open MixedTwoPointTemplateWeight TwoPointSplitCanonicalQuotient
open TwoPointSplitFaceContraction TwoPointSplitFaceWeight
open InteriorGraphFaceCoordinates TwoPointBinaryFaceAdmissibility
open scoped Classical BigOperators

variable {n : ℕ} (Γ : Graph (fun _ : Fin (n + 1) => 2) 2)
    (v : Fin (n + 1)) (c : Fin 3) (χ : Γ.VertexSplitChoices v)
    {i a b : Fin (n + 2)}
    (ha : a ∈ cluster v) (hb : b ∈ cluster v) (hba : b ≠ a)
    (hanchor : i ∈ cluster v → a = i)

/-- Genuine source templates satisfy all contraction conditions themselves;
the canonical face integral needs no nonzero-density witness. -/
theorem normalized_sourceMajor :
    normalizedIntegral v (Γ.vertexSplit (sourceTemplate c) v rfl χ)
      (MixedSourceFaceSign.sourceMajorOrder v ha hb hba hanchor) =
      (if c = 1 then (-1 : ℝ) else 1) * GraphCanonicalBinaryWeights.rawBinaryWeight (n + 1) Γ := by
  let H := Γ.vertexSplit (sourceTemplate c) v rfl χ
  let order := MixedSourceFaceSign.sourceMajorOrder v ha hb hba hanchor
  let D := TwoPointTemplateAdmissibility.source_data Γ v c χ
  let hc := TwoPointTemplateAdmissibility.count_shape_of_data v H D ha hb hba order
  have h := normalized_integral_original v rfl Γ (sourceTemplate c) χ (sourceLeg c)
    (source_leg c) MixedTwoPointFaceWeight.vectorBivector_edgeCount D ha hb hba hanchor order hc
  have hf : GeometricWeights.outgoingFactor (fun _ : Fin (n + 1) => 2) ≠ 0 := by
    unfold GeometricWeights.outgoingFactor
    apply Finset.prod_ne_zero_iff.mpr
    intro w _
    exact inv_ne_zero (by norm_num)
  rw [VertexSplitOutgoingFactor.vector_bivector_split_factor _ v rfl,
    div_self hf, one_mul] at h
  have hs := MixedSourceFaceSign.faceSign_sourceMajor Γ v c χ D ha hb hba hanchor order hc rfl
  change faceSign v rfl H MixedTwoPointFaceWeight.vectorBivector_edgeCount D ha hanchor order hc *
    permutationSign (R := ℝ)
      (slotPermutation v rfl Γ (sourceTemplate c) χ (sourceLeg c) (source_leg c)
        MixedTwoPointFaceWeight.vectorBivector_edgeCount D) = _ at hs
  rw [hs] at h
  exact h

end EnvelopingIsomorphism.Deformation.Kontsevich.MixedSourceTemplateIntegral
