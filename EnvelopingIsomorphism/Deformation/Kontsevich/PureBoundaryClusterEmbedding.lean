import EnvelopingIsomorphism.Deformation.Kontsevich.PureBoundaryClusterDomain

/-! A genuine topological embedding of the pure external cluster domain.
Finite endpoint positions recover center and radius; the fixed unit reference
pair recovers all shape coordinates continuously through radius zero. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.PureBoundaryClusterDomain

open Configuration Topology Set

variable {n m : ℕ} {i : Fin n} {l u : Fin (m + 1)} {a b : Fin m}

def scaledVertex (x : PureBoundaryClusterDomain i m l u a b) (v : Fin n ⊕ Fin m) : ℂ :=
  x.datum.doubledBase (Sum.inl v) + (x.scale : ℂ) * x.datum.doubledVelocity (Sum.inl v)

theorem insertion_position (x : PureBoundaryClusterDomain i m l u a b) (v : Fin n ⊕ Fin m) :
    x.insertion.val.1 v = (x.scaledVertex v : OnePoint ℂ) := rfl

theorem scaledVertex_interior (x : PureBoundaryClusterDomain i m l u a b) (j : Fin n) :
    x.scaledVertex (Sum.inl j) = (x.datum.interior j : ℂ) := by
  simp [scaledVertex, PureBoundaryClusterData.doubledBase, PureBoundaryClusterData.doubledVelocity]

theorem scaledVertex_boundary (x : PureBoundaryClusterDomain i m l u a b) (j : Fin m) :
    x.scaledVertex (Sum.inr j) = (x.datum.scaledBoundary x.scale j : ℂ) := by
  simp [scaledVertex, PureBoundaryClusterData.doubledBase, PureBoundaryClusterData.doubledVelocity,
    PureBoundaryClusterData.scaledBoundary]

/-- The actual stored compact coordinates force continuity of every parameter. -/
theorem continuous_of_continuous_insertion {Y : Type*} [TopologicalSpace Y]
    (f : Y → PureBoundaryClusterDomain i m l u a b)
    (hf : Continuous (fun y => (f y).insertion)) : Continuous f := by
  classical
  by_cases hba : b ≠ a
  · have hc : Continuous (fun y => ((f y).insertion.val : CompactCoordinateSpace n m)) :=
      continuous_subtype_val.comp hf
    have hpos (v : Fin n ⊕ Fin m) : Continuous (fun y => (f y).scaledVertex v) := by
      apply (OnePoint.isOpenEmbedding_coe (X := ℂ)).isEmbedding.continuous_iff.mpr
      change Continuous (fun y => ((f y).scaledVertex v : OnePoint ℂ))
      have h : Continuous (fun y => (f y).insertion.val.1 v) :=
        (continuous_apply v).comp (continuous_fst.comp hc)
      simpa only [insertion_position] using h
    have hboundary (j : Fin m) : Continuous (fun y => (f y).datum.scaledBoundary (f y).scale j) := by
      simpa only [Function.comp_def, scaledVertex_boundary, Complex.ofReal_re] using
        Complex.continuous_re.comp (hpos (Sum.inr j))
    have hinterior (j : Fin n) : Continuous (fun y => ((f y).datum.interior j : ℂ)) := by
      simpa only [scaledVertex_interior] using hpos (Sum.inl j)
    have hcenter : Continuous (fun y => (f y).datum.center) := by
      simpa only [PureBoundaryClusterData.scaledBoundary_left] using hboundary a
    have hr : Continuous (fun y => (f y).scale) := by
      have h := (hboundary b).sub (hboundary a)
      change Continuous (fun y => (f y).datum.scaledBoundary (f y).scale b -
        (f y).datum.scaledBoundary (f y).scale a) at h
      simpa only [PureBoundaryClusterData.scaledBoundary_endpoint_gap] using h
    have hshape (j : Fin m) (hj : j ∈ boundaryClusterBlock l u) (hja : j ≠ a) :
        Continuous (fun y => ((f y).datum.boundaryVelocity j : ℂ)) := by
      have hphase : Continuous (fun y =>
          (f y).insertion.val.2.1 (PureBoundaryClusterData.shapePair a j hja)) :=
        (continuous_apply _).comp (continuous_fst.comp (continuous_snd.comp hc))
      have hratio : Continuous (fun y =>
          ((f y).insertion.val.2.2 (PureBoundaryClusterData.shapeTriple a b j hja hba) : ℝ)) :=
        continuous_subtype_val.comp ((continuous_apply _).comp
          (continuous_snd.comp (continuous_snd.comp hc)))
      have hlt (y : Y) :
          ((f y).insertion.val.2.2 (PureBoundaryClusterData.shapeTriple a b j hja hba) : ℝ) < 1 :=
        (f y).datum.resolvedCoordinates_shape_ratio_lt_one (f y).scale j hj hja hba
      have hp : Continuous (fun y =>
          ((f y).insertion.val.2.1 (PureBoundaryClusterData.shapePair a j hja),
            (⟨((f y).insertion.val.2.2 (PureBoundaryClusterData.shapeTriple a b j hja hba) : ℝ),
              hlt y⟩ : Set.Iio (1 : ℝ)))) := hphase.prodMk (hratio.subtype_mk hlt)
      have hrec := continuous_recoverRelativePosition.comp hp
      simpa only [Function.comp_def, insertion, PureBoundaryClusterData.compactInsertion,
        PureBoundaryClusterData.recover_shape _ _ j hj hja hba] using hrec
    have hvelocity (j : Fin m) : Continuous (fun y => (f y).datum.boundaryVelocity j) := by
      by_cases hj : j ∈ boundaryClusterBlock l u
      · by_cases hja : j = a
        · have heq : (fun y => (f y).datum.boundaryVelocity j) = fun _ : Y => (0 : ℝ) := by
            funext y
            simpa only [hja] using (f y).datum.boundaryVelocity_left
          rw [heq]
          exact continuous_const
        · simpa only [Function.comp_def, Complex.ofReal_re] using
            Complex.continuous_re.comp (hshape j hj hja)
      · have heq : (fun y => (f y).datum.boundaryVelocity j) = fun _ : Y => (0 : ℝ) := by
          funext y
          exact (f y).datum.boundaryVelocity_zero_off j hj
        rw [heq]
        exact continuous_const
    have hbase (j : Fin m) : Continuous (fun y => (f y).datum.boundaryBase j) := by
      have h := (hboundary j).sub (hr.mul (hvelocity j))
      change Continuous (fun y => (f y).datum.scaledBoundary (f y).scale j -
        (f y).scale * (f y).datum.boundaryVelocity j) at h
      simpa only [PureBoundaryClusterData.scaledBoundary, add_sub_cancel_right] using h
    apply IsEmbedding.subtypeVal.continuous_iff.mpr
    change Continuous (fun y => ((f y).datum, (f y).scale))
    apply Continuous.prodMk _ hr
    apply PureBoundaryClusterData.isEmbedding_coordinates.continuous_iff.mpr
    exact hcenter.prodMk ((continuous_pi hinterior).prodMk
      ((continuous_pi hbase).prodMk (continuous_pi hvelocity)))
  · letI : IsEmpty Y := ⟨fun y => hba (f y).datum.endpoint_lt.ne'⟩
    exact continuous_of_discreteTopology

def rangeHomeomorph : PureBoundaryClusterDomain i m l u a b ≃ₜ
    Set.range (insertion : PureBoundaryClusterDomain i m l u a b → Compactification i m) := by
  let e := Equiv.ofInjective (insertion : PureBoundaryClusterDomain i m l u a b → Compactification i m)
    insertion_injective
  refine ⟨e, ?_, ?_⟩
  · exact continuous_insertion.subtype_mk _
  · apply continuous_of_continuous_insertion e.symm
    have heq : (fun y => (e.symm y).insertion) = Subtype.val := by
      funext y
      exact congrArg Subtype.val (e.apply_symm_apply y)
    rw [heq]
    exact continuous_subtype_val

theorem isEmbedding_insertion :
    IsEmbedding (insertion : PureBoundaryClusterDomain i m l u a b → Compactification i m) :=
  IsEmbedding.subtypeVal.comp rangeHomeomorph.isEmbedding

end EnvelopingIsomorphism.Deformation.Kontsevich.PureBoundaryClusterDomain
