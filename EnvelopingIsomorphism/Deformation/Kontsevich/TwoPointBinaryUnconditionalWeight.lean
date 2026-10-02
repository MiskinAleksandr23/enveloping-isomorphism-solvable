import EnvelopingIsomorphism.Deformation.Kontsevich.TwoPointBinaryFaceWeight

/-! Unconditional adjacent binary two-point matching. Admissible faces use
the actual extracted quotient; every other actual face density vanishes. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace EnvelopingIsomorphism.Deformation.Kontsevich.TwoPointBinaryUnconditionalWeight
open KontsevichGraph.General UniformBinaryGraphs UniformBinaryContraction
open InteriorGraphFaceCoordinates TwoPointBinaryFaceAdmissibility TwoPointQuotientEdgeOrder
open TwoPointBinaryFaceWeight MeasureTheory Set
open scoped Classical
variable {n : ℕ} (v : Fin (n+1)) (H : BinaryGraph (n+2) 3)
  {i a b : Fin (n+2)} (ha : a ∈ cluster v) (hb : b ∈ cluster v) (hba : b ≠ a)
  (hanchor : i ∈ cluster v → a = i)

/-- The actual unique internal arrow gives the native count, for any genuine
edge enumeration. No count premise is needed. -/
theorem internal_count_of_unique {d : ℕ}
    (order : Fin d ≃ KontsevichGraph.General.Edge (fun _ : Fin (n+2) => 2))
    (c s : Fin 2) (hi : UniqueInternalAt v H c s) :
    Fintype.card {j // IsInternal (cluster v) (TwoPointBinaryFaceAdmissibility.orderedEdges H order j)} = 1 := by
  apply Fintype.card_eq_one_iff.mpr
  let e : KontsevichGraph.General.Edge (fun _ : Fin (n+2) => 2) := ⟨vertexSplitChild v c,s⟩
  have he : IsInternal (cluster v) (TwoPointBinaryFaceAdmissibility.orderedEdges H order (order.symm e)) := by
    change IsInternal (cluster v) ((order (order.symm e)).1,H.target (order (order.symm e)))
    rw [Equiv.apply_symm_apply]
    exact (isInternal_iff_slot v H c s hi e).mpr rfl
  refine ⟨⟨order.symm e,he⟩, ?_⟩
  intro j
  apply Subtype.ext
  apply order.injective
  rw [Equiv.apply_symm_apply]
  exact (isInternal_iff_slot v H c s hi (order j.val)).mp j.property

include ha hb hba in
/-- A failure of the concrete contraction admissibility forces zero at each
point of the actual integration domain. -/
theorem density_zero_of_not_admissible
    (order : Fin (shapeDegree a b (cluster v) + coarseDegree i a (cluster v) 3) ≃
      KontsevichGraph.General.Edge (fun _ : Fin (n+2) => 2))
    (hbad : ¬ AdmissiblePair v H)
    (y : RealProductCoordinates i a b (cluster v) 3)
    (hy : y ∈ InteriorFiberAngleSplit.integrationRegion (shapeN a b (cluster v)) ×ˢ
      GeometricWeights.realDomain (coarseN i a (cluster v)) 3) :
    realFaceDensity (TwoPointBinaryFaceAdmissibility.orderedEdges H order) y = 0 := by
  by_contra h
  exact hbad (exists_contractionData_of_density_ne_zero v H order ha hb hba y hy h)

include ha hb hba in
theorem normalizedIntegral_zero_of_not_admissible
    (order : Fin (shapeDegree a b (cluster v) + coarseDegree i a (cluster v) 3) ≃
      KontsevichGraph.General.Edge (fun _ : Fin (n+2) => 2))
    (hbad : ¬ AdmissiblePair v H) : normalizedIntegral v H order = 0 := by
  unfold normalizedIntegral
  rw [setIntegral_eq_zero_of_forall_eq_zero
    (density_zero_of_not_admissible v H ha hb hba order hbad)]
  simp

/-- Every binary graph has exactly the physical-pair coefficient prescribed
by its genuine canonical native face integral, including all inadmissible graphs. -/
theorem normalized_integral_eq_physicalCoefficient :
    normalizedIntegral v H (sourceMajorOrder v ha hb hba hanchor) =
      (3 / 2 : ℝ) * GraphCurvaturePhysicalPairs.physicalCoefficient H
        (GraphCurvatureLabelCounting.movedPair v (Equiv.refl _)) := by
  by_cases hadm : AdmissiblePair v H
  · obtain ⟨c,s,hi,hd,hx⟩ := hadm
    have hcount : Fintype.card {j // IsInternal (cluster v)
        (TwoPointBinaryFaceAdmissibility.orderedEdges H (sourceMajorOrder v ha hb hba hanchor) j)} =
        shapeDegree a b (cluster v) := by
      rw [internal_count_of_unique v H _ c s hi, shapeDegree_eq ha hb hba, cluster_card]
    exact normalized_integral_sourceMajor_eq_physicalCoefficient v H ha hb hba hanchor _ hcount c s hi hd hx rfl
  · rw [normalizedIntegral_zero_of_not_admissible v H ha hb hba _ hadm]
    have hz := GraphCurvaturePhysicalPairs.physicalCoefficient_zero_of_not_admissible H
      (GraphCurvatureLabelCounting.movedPair v (Equiv.refl _)) ⟨(v,Equiv.refl _),rfl⟩
      (by simpa only [Equiv.refl_symm, KontsevichGraph.General.Graph.permuteInternal_refl] using hadm)
    rw [hz, mul_zero]

end EnvelopingIsomorphism.Deformation.Kontsevich.TwoPointBinaryUnconditionalWeight
