import EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryAnchoredInfinityChart

/-! The full stored data recover all infinity-chart parameters continuously,
including the radial scale at zero. This proves the actual insertion is an
embedding, without a supplied inverse or image-coverage hypothesis. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryAnchoredInfinityDomain

open Configuration Topology Set

variable {n m : ℕ} {a : Fin n} {l u : Fin (m + 1)} {o : Fin m}

theorem insertion_injective :
    Function.Injective (insertion : BoundaryAnchoredInfinityDomain a m l u o → Compactification a m) := by
  intro x y hxy
  have hcoords : x.coordinates = y.coordinates := by
    simpa only [insertion_projectDR] using congrArg (fun z : Compactification a m ↦ projectDR z.val) hxy
  have hr : x.scale = y.scale := by
    have h := congrArg (fun z : DRData n m ↦ recoverReferenceHeight
      (BoundaryAnchoredInfinityData.referenceSign l o) (z.1 (harmonicDenominatorPair a (Sum.inr o)))) hcoords
    change recoverReferenceHeight _ ((x.datum.resolvedDR x.scale).1 _) =
      recoverReferenceHeight _ ((y.datum.resolvedDR y.scale).1 _) at h
    rwa [x.datum.recover_scale, y.datum.recover_scale] at h
  have hshape : x.datum.shape = y.datum.shape := by
    funext j
    apply UpperHalfPlane.ext
    have h := congrArg (fun z : Compactification a m ↦ z.val.1 (Sum.inl j)) hxy
    rw [insertion_shape, insertion_shape] at h
    exact OnePoint.coe_injective h
  have hvel : x.datum.boundaryVelocity = y.datum.boundaryVelocity := by
    funext j
    by_cases hj : j ∈ boundaryClusterBlock l u
    · have h := congrArg (fun z : Compactification a m ↦ z.val.1 (Sum.inr j)) hxy
      rw [insertion_boundary_inside x j hj, insertion_boundary_inside y j hj] at h
      exact Complex.ofReal_injective (OnePoint.coe_injective h)
    · rw [x.datum.boundaryVelocity_zero_off j hj, y.datum.boundaryVelocity_zero_off j hj]
  have hbase : x.datum.boundaryBase = y.datum.boundaryBase := by
    funext j
    by_cases hj : j ∈ boundaryClusterBlock l u
    · rw [x.datum.boundaryBase_zero_on j hj, y.datum.boundaryBase_zero_on j hj]
    · have hx := x.datum.recover_outside_base x.scale j hj
      have hy := y.datum.recover_outside_base y.scale j hj
      change ((‖(BoundaryAnchoredInfinityData.referenceSign l o : ℂ) + (x.scale : ℂ) * Complex.I‖ : ℂ) *
        recoverRelativePosition (x.coordinates.1 (harmonicDenominatorPair a (Sum.inr j)))
          (x.coordinates.2 (boundaryRatioTriple a j o))).re = _ at hx
      rw [hcoords, hr] at hx
      exact hx.symm.trans hy
  apply Subtype.ext
  exact Prod.ext (BoundaryAnchoredInfinityData.ext hshape hbase hvel) hr

/-- Continuity of the insertion forces continuity of every original chart parameter,
by the proved phase and norm-ratio inverse formulas. -/
theorem continuous_of_continuous_insertion {Y : Type*} [TopologicalSpace Y]
    (f : Y → BoundaryAnchoredInfinityDomain a m l u o)
    (hf : Continuous (fun y ↦ (f y).insertion)) : Continuous f := by
  have hcompact : Continuous (fun y ↦ ((f y).insertion.val : CompactCoordinateSpace n m)) :=
    continuous_subtype_val.comp hf
  have hdr : Continuous (fun y ↦ (f y).coordinates) := by
    simpa only [Function.comp_def, insertion_projectDR] using continuous_projectDR.comp hcompact
  have hphase (j : Fin m) : Continuous (fun y ↦ (f y).coordinates.1 (harmonicDenominatorPair a (Sum.inr j))) :=
    (continuous_apply _).comp (continuous_fst.comp hdr)
  have hratio (j : Fin m) : Continuous (fun y ↦ ((f y).coordinates.2 (boundaryRatioTriple a j o) : ℝ)) :=
    continuous_subtype_val.comp ((continuous_apply _).comp (continuous_snd.comp hdr))
  have hshape (j : Fin n) : Continuous (fun y ↦ ((f y).datum.shape j : ℂ)) := by
    apply (OnePoint.isOpenEmbedding_coe (X := ℂ)).isEmbedding.continuous_iff.mpr
    change Continuous (fun y ↦ (((f y).datum.shape j : ℂ) : OnePoint ℂ))
    have hp := (continuous_apply (Sum.inl j)).comp (continuous_fst.comp hcompact)
    simpa only [Function.comp_def, insertion_shape] using hp
  have hr : Continuous (fun y ↦ (f y).scale) := by
    have hre := Complex.continuous_re.comp (continuous_subtype_val.comp (hphase o))
    have him := Complex.continuous_im.comp (continuous_subtype_val.comp (hphase o))
    have hne (y : Y) : ((f y).coordinates.1 (harmonicDenominatorPair a (Sum.inr o)) : ℂ).re ≠ 0 :=
      (f y).datum.resolvedDR_reference_re_ne_zero (f y).scale
    have hrec : Continuous (fun y ↦ recoverReferenceHeight
        (BoundaryAnchoredInfinityData.referenceSign l o)
        ((f y).coordinates.1 (harmonicDenominatorPair a (Sum.inr o)))) :=
      (continuous_const.mul him).div hre hne
    simpa only [coordinates, BoundaryAnchoredInfinityData.recover_scale] using hrec
  have hnorm : Continuous (fun y ↦
      (‖(BoundaryAnchoredInfinityData.referenceSign l o : ℂ) + ((f y).scale : ℂ) * Complex.I‖ : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_norm.comp
      (continuous_const.add ((Complex.continuous_ofReal.comp hr).mul continuous_const)))
  have hbase (j : Fin m) : Continuous (fun y ↦ (f y).datum.boundaryBase j) := by
    by_cases hj : j ∈ boundaryClusterBlock l u
    · have hz : (fun y ↦ (f y).datum.boundaryBase j) = fun _ ↦ (0 : ℝ) := by
        funext y
        exact (f y).datum.boundaryBase_zero_on j hj
      rw [hz]
      exact continuous_const
    · have hlt (y : Y) : ((f y).coordinates.2 (boundaryRatioTriple a j o) : ℝ) < 1 :=
        (f y).datum.resolvedDR_outside_ratio_lt_one (f y).scale j hj
      have hpair : Continuous (fun y ↦
          ((f y).coordinates.1 (harmonicDenominatorPair a (Sum.inr j)),
            (⟨((f y).coordinates.2 (boundaryRatioTriple a j o) : ℝ), hlt y⟩ : Set.Iio (1 : ℝ)))) :=
        (hphase j).prodMk ((hratio j).subtype_mk hlt)
      have hrec := continuous_recoverRelativePosition.comp hpair
      have h := Complex.continuous_re.comp (hnorm.mul hrec)
      change Continuous (fun y ↦
        ((‖(BoundaryAnchoredInfinityData.referenceSign l o : ℂ) + ((f y).scale : ℂ) * Complex.I‖ : ℂ) *
          recoverRelativePosition
            ((f y).coordinates.1 (harmonicDenominatorPair a (Sum.inr j)))
            ((f y).coordinates.2 (boundaryRatioTriple a j o))).re) at h
      simpa only [coordinates, BoundaryAnchoredInfinityData.recover_outside_base _ _ j hj] using h
  have hvel (j : Fin m) : Continuous (fun y ↦ (f y).datum.boundaryVelocity j) := by
    by_cases hj : j ∈ boundaryClusterBlock l u
    · have hc : Continuous (fun y ↦ ((f y).datum.boundaryVelocity j : ℂ)) := by
        apply (OnePoint.isOpenEmbedding_coe (X := ℂ)).isEmbedding.continuous_iff.mpr
        change Continuous (fun y ↦ (((f y).datum.boundaryVelocity j : ℂ) : OnePoint ℂ))
        have hp := (continuous_apply (Sum.inr j)).comp (continuous_fst.comp hcompact)
        simpa only [Function.comp_def, insertion_boundary_inside _ j hj] using hp
      simpa only [Function.comp_def, Complex.ofReal_re] using Complex.continuous_re.comp hc
    · have hz : (fun y ↦ (f y).datum.boundaryVelocity j) = fun _ ↦ (0 : ℝ) := by
        funext y
        exact (f y).datum.boundaryVelocity_zero_off j hj
      rw [hz]
      exact continuous_const
  apply IsEmbedding.subtypeVal.continuous_iff.mpr
  change Continuous (fun y ↦ ((f y).datum, (f y).scale))
  apply Continuous.prodMk _ hr
  apply BoundaryAnchoredInfinityData.isEmbedding_coords.continuous_iff.mpr
  exact (continuous_pi hshape).prodMk ((continuous_pi hbase).prodMk (continuous_pi hvel))

def rangeHomeomorph : BoundaryAnchoredInfinityDomain a m l u o ≃ₜ
    Set.range (insertion : BoundaryAnchoredInfinityDomain a m l u o → Compactification a m) := by
  let e := Equiv.ofInjective (insertion : BoundaryAnchoredInfinityDomain a m l u o → Compactification a m)
    insertion_injective
  refine ⟨e, continuous_insertion.subtype_mk _, ?_⟩
  apply continuous_of_continuous_insertion e.symm
  have heq : (fun y ↦ (e.symm y).insertion) = Subtype.val := by
    funext y
    exact congrArg Subtype.val (e.apply_symm_apply y)
  rw [heq]
  exact continuous_subtype_val

theorem isEmbedding_insertion :
    IsEmbedding (insertion : BoundaryAnchoredInfinityDomain a m l u o → Compactification a m) :=
  IsEmbedding.subtypeVal.comp rangeHomeomorph.isEmbedding

end EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryAnchoredInfinityDomain
