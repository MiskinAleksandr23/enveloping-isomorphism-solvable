import EnvelopingIsomorphism.Deformation.Kontsevich.NormalizedInteriorClusterSlice

/-!
# The normalized single-cluster slice is an actual topological embedding

The inverse is continuous on the image: finite position entries recover scaled
positions, direction/ratio entries recover velocities, the reference displacement
recovers the scale, and subtraction recovers coarse positions. No image-openness
or atlas-coverage statement is used.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.NormalizedInteriorClusterSlice

open Configuration Topology Set

variable {n m : ℕ} {i : Fin n} {S : Finset (Fin n)} {a b : Fin n}

/-- Continuity of the compact coordinates forces continuity of all normalized parameters. -/
theorem continuous_of_continuous_insertion {Y : Type*} [TopologicalSpace Y]
    (f : Y → NormalizedInteriorClusterSlice i m S a b)
    (ha : a ∈ S) (hb : b ∈ S) (hba : b ≠ a)
    (hf : Continuous (fun y => (f y).insertion)) : Continuous f := by
  have hc : Continuous (fun y => ((f y).insertion.val : CompactCoordinateSpace n m)) :=
    continuous_subtype_val.comp hf
  have hpos (j : Fin n) : Continuous (fun y => (f y).scaledPosition j) := by
    apply (OnePoint.isOpenEmbedding_coe (X := ℂ)).isEmbedding.continuous_iff.mpr
    change Continuous (fun y => ((f y).scaledPosition j : OnePoint ℂ))
    have h : Continuous (fun y => (f y).insertion.val.1 (Sum.inl j)) :=
      (continuous_apply (Sum.inl j)).comp (continuous_fst.comp hc)
    simpa only [insertion_position] using h
  have hvel (j : Fin n) : Continuous (fun y => (f y).val.datum.velocity j) := by
    by_cases hj : j ∈ S
    · by_cases hja : j = a
      · have heq : (fun y => (f y).val.datum.velocity j) = fun _ : Y => (0 : ℂ) := by
          funext y
          simpa only [hja] using (f y).property.1
        rw [heq]
        exact continuous_const
      · have hphase : Continuous (fun y => complexPhase ((f y).val.datum.velocity j)) := by
          have h : Continuous (fun y => (f y).insertion.val.2.1 (shapePair (m := m) a j hja)) :=
            (continuous_apply _).comp (continuous_fst.comp (continuous_snd.comp hc))
          simpa only [insertion_shape_direction _ ha j hj hja] using h
        have hratio : Continuous (fun y => unitNormRatio ((f y).val.datum.velocity j)) := by
          have h : Continuous (fun y =>
              ((f y).insertion.val.2.2 (shapeTriple (m := m) a b j hja hba) : ℝ)) :=
            continuous_subtype_val.comp ((continuous_apply _).comp
              (continuous_snd.comp (continuous_snd.comp hc)))
          simpa only [insertion_shape_ratio _ ha hb j hj hja hba] using h
        have hpair : Continuous (fun y =>
            (complexPhase ((f y).val.datum.velocity j),
              (⟨unitNormRatio ((f y).val.datum.velocity j), unitNormRatio_lt_one _⟩ : Set.Iio (1 : ℝ)))) :=
          hphase.prodMk (hratio.subtype_mk _)
        simpa only [Function.comp_def, recoverRelativePosition_phase_ratio] using
          continuous_recoverRelativePosition.comp hpair
    · have heq : (fun y => (f y).val.datum.velocity j) = fun _ : Y => (0 : ℂ) := by
        funext y
        exact (f y).val.datum.velocity_zero_off j hj
      rw [heq]
      exact continuous_const
  have hr : Continuous (fun y => (f y).val.scale) := by
    have h := ((hpos b).sub (hpos a)).norm
    simpa only [Pi.sub_apply, norm_reference_displacement _ ha hb] using h
  have hbase (j : Fin n) : Continuous (fun y => ((f y).val.datum.base j : ℂ)) := by
    have h := (hpos j).sub ((Complex.continuous_ofReal.comp hr).mul (hvel j))
    change Continuous (fun y => (f y).scaledPosition j -
      ((f y).val.scale : ℂ) * (f y).val.datum.velocity j) at h
    simpa only [scaledPosition, add_sub_cancel_right] using h
  have hboundary (j : Fin m) : Continuous (fun y => (f y).val.datum.boundary j) := by
    have hc : Continuous (fun y => ((f y).val.datum.boundary j : ℂ)) := by
      apply (OnePoint.isOpenEmbedding_coe (X := ℂ)).isEmbedding.continuous_iff.mpr
      change Continuous (fun y => (((f y).val.datum.boundary j : ℂ) : OnePoint ℂ))
      have h : Continuous (fun y => (f y).insertion.val.1 (Sum.inr j)) :=
        (continuous_apply (Sum.inr j)).comp (continuous_fst.comp hc)
      simpa only [insertion_boundary] using h
    simpa only [Function.comp_def, Complex.ofReal_re] using Complex.continuous_re.comp hc
  apply IsEmbedding.subtypeVal.continuous_iff.mpr
  change Continuous (fun y => (f y).val)
  apply IsEmbedding.subtypeVal.continuous_iff.mpr
  change Continuous (fun y => ((f y).val.datum, (f y).val.scale))
  apply Continuous.prodMk _ hr
  apply SingleInteriorCluster.isEmbedding_toInteriorCollisionData.continuous_iff.mpr
  change Continuous (fun y => (f y).val.datum.toInteriorCollisionData)
  apply InteriorCollisionData.isEmbedding_coordinates.continuous_iff.mpr
  exact (continuous_pi hbase).prodMk ((continuous_pi hvel).prodMk (continuous_pi hboundary))

/-- The actual inverse parameter map on the image is continuous. -/
def rangeHomeomorph (ha : a ∈ S) (hb : b ∈ S) (hba : b ≠ a) :
    NormalizedInteriorClusterSlice i m S a b ≃ₜ
      Set.range (insertion : NormalizedInteriorClusterSlice i m S a b → Compactification i m) := by
  let e := Equiv.ofInjective (insertion : NormalizedInteriorClusterSlice i m S a b → Compactification i m)
    (insertion_injective ha hb hba)
  refine ⟨e, ?_, ?_⟩
  · exact continuous_insertion.subtype_mk _
  · apply continuous_of_continuous_insertion e.symm ha hb hba
    have heq : (fun y => (e.symm y).insertion) = Subtype.val := by
      funext y
      exact congrArg Subtype.val (e.apply_symm_apply y)
    rw [heq]
    exact continuous_subtype_val

/-- The normalized arbitrary-cluster insertion is a topological embedding through scale zero. -/
theorem isEmbedding_insertion (ha : a ∈ S) (hb : b ∈ S) (hba : b ≠ a) :
    IsEmbedding (insertion : NormalizedInteriorClusterSlice i m S a b → Compactification i m) :=
  IsEmbedding.subtypeVal.comp (rangeHomeomorph ha hb hba).isEmbedding

end EnvelopingIsomorphism.Deformation.Kontsevich.NormalizedInteriorClusterSlice
