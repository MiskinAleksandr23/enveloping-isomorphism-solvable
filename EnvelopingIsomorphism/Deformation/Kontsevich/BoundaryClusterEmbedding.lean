import EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryClusterChart

/-! A genuine topological embedding for one finite real cluster.
Finite position coordinates recover the center and radius. The explicit
direction/ratio inverse recovers all inner shape coordinates continuously,
including at radius zero. No openness or coverage premise is used. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryClusterDomain

open Configuration Topology Set

variable {n m : ℕ} {i a : Fin n} {S : Finset (Fin n)} {l u : Fin (m + 1)}

def scaledVertex (x : BoundaryClusterDomain i a m S l u) (v : Fin n ⊕ Fin m) : ℂ :=
  x.datum.baseVertex v + (x.scale : ℂ) * x.datum.velocityVertex v

theorem insertion_position (x : BoundaryClusterDomain i a m S l u) (v : Fin n ⊕ Fin m) :
    x.insertion.val.1 v = (x.scaledVertex v : OnePoint ℂ) := rfl

theorem scaledVertex_anchor (x : BoundaryClusterDomain i a m S l u) :
    x.scaledVertex (Sum.inl a) = (x.datum.center : ℂ) + (x.scale : ℂ) * Complex.I := by
  simp only [scaledVertex, BoundaryClusterData.baseVertex, BoundaryClusterData.velocityVertex,
    BoundaryClusterData.doubledBase, BoundaryClusterData.doubledVelocity,
    x.datum.base_eq_center a x.datum.anchor_mem, x.datum.velocity_anchor]

/-- The stored coordinates force continuity of every normalized geometric parameter. -/
theorem continuous_of_continuous_insertion {Y : Type*} [TopologicalSpace Y]
    (f : Y → BoundaryClusterDomain i a m S l u)
    (hf : Continuous (fun y => (f y).insertion)) : Continuous f := by
  have hc : Continuous (fun y => ((f y).insertion.val : CompactCoordinateSpace n m)) :=
    continuous_subtype_val.comp hf
  have hpos (v : Fin n ⊕ Fin m) : Continuous (fun y => (f y).scaledVertex v) := by
    apply (OnePoint.isOpenEmbedding_coe (X := ℂ)).isEmbedding.continuous_iff.mpr
    change Continuous (fun y => ((f y).scaledVertex v : OnePoint ℂ))
    have h : Continuous (fun y => (f y).insertion.val.1 v) :=
      (continuous_apply v).comp (continuous_fst.comp hc)
    simpa only [insertion_position] using h
  have hshape (v : Fin n ⊕ Fin m)
      (hv : ∀ y, (f y).datum.baseVertex v = ((f y).datum.center : ℂ)) :
      Continuous (fun y => (f y).datum.velocityVertex v) := by
    have hphase : Continuous (fun y => (f y).insertion.val.2.1 (harmonicDenominatorPair a v)) :=
      (continuous_apply _).comp (continuous_fst.comp (continuous_snd.comp hc))
    have hratio : Continuous (fun y =>
        ((f y).insertion.val.2.2 (BoundaryClusterData.shapeTriple a v) : ℝ)) :=
      continuous_subtype_val.comp ((continuous_apply _).comp
        (continuous_snd.comp (continuous_snd.comp hc)))
    have hlt (y : Y) : ((f y).insertion.val.2.2 (BoundaryClusterData.shapeTriple a v) : ℝ) < 1 :=
      (f y).datum.resolvedCoordinates_shape_ratio_lt_one (f y).scale v (hv y)
    have hp : Continuous (fun y =>
        ((f y).insertion.val.2.1 (harmonicDenominatorPair a v),
          (⟨((f y).insertion.val.2.2 (BoundaryClusterData.shapeTriple a v) : ℝ), hlt y⟩ : Set.Iio (1 : ℝ)))) :=
      hphase.prodMk (hratio.subtype_mk hlt)
    have hrec := continuous_recoverRelativePosition.comp hp
    have h := ((continuous_const (y := (2 : ℂ))).mul hrec).sub (continuous_const (y := Complex.I))
    change Continuous (fun y => (2 : ℂ) * recoverRelativePosition
      ((f y).insertion.val.2.1 (harmonicDenominatorPair a v))
      ((f y).insertion.val.2.2 (BoundaryClusterData.shapeTriple a v)) - Complex.I) at h
    simpa only [insertion, BoundaryClusterData.compactInsertion,
      BoundaryClusterData.recover_shape _ _ _ (hv _)] using h
  have hvel (j : Fin n) : Continuous (fun y => (f y).datum.velocity j) := by
    by_cases hj : j ∈ S
    · exact hshape (Sum.inl j) (fun y => (f y).datum.base_eq_center j hj)
    · have heq : (fun y => (f y).datum.velocity j) = fun _ : Y => (0 : ℂ) := by
        funext y
        exact (f y).datum.velocity_zero_off j hj
      rw [heq]
      exact continuous_const
  have hbvel (j : Fin m) : Continuous (fun y => (f y).datum.boundaryVelocity j) := by
    by_cases hj : j ∈ boundaryClusterBlock l u
    · have hv := hshape (Sum.inr j) (fun y =>
        congrArg Complex.ofReal ((f y).datum.boundaryBase_eq_center j hj))
      simpa only [Function.comp_def, BoundaryClusterData.velocityVertex,
        BoundaryClusterData.doubledVelocity, Complex.ofReal_re] using Complex.continuous_re.comp hv
    · have heq : (fun y => (f y).datum.boundaryVelocity j) = fun _ : Y => (0 : ℝ) := by
        funext y
        exact (f y).datum.boundaryVelocity_zero_off j hj
      rw [heq]
      exact continuous_const
  have hcenter : Continuous (fun y => (f y).datum.center) := by
    simpa only [Function.comp_def, scaledVertex_anchor, Complex.add_re,
      Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im,
      mul_zero, zero_mul, sub_zero, add_zero] using Complex.continuous_re.comp (hpos (Sum.inl a))
  have hr : Continuous (fun y => (f y).scale) := by
    simpa only [Function.comp_def, scaledVertex_anchor, Complex.add_im,
      Complex.ofReal_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_im,
      mul_one, zero_mul, add_zero, zero_add] using Complex.continuous_im.comp (hpos (Sum.inl a))
  have hbase (j : Fin n) : Continuous (fun y => (f y).datum.base j) := by
    have h := (hpos (Sum.inl j)).sub ((Complex.continuous_ofReal.comp hr).mul (hvel j))
    change Continuous (fun y => (f y).scaledVertex (Sum.inl j) -
      ((f y).scale : ℂ) * (f y).datum.velocity j) at h
    simpa only [scaledVertex, BoundaryClusterData.baseVertex, BoundaryClusterData.velocityVertex,
      BoundaryClusterData.doubledBase, BoundaryClusterData.doubledVelocity, add_sub_cancel_right] using h
  have hbbase (j : Fin m) : Continuous (fun y => (f y).datum.boundaryBase j) := by
    have h := (hpos (Sum.inr j)).sub
      ((Complex.continuous_ofReal.comp hr).mul (Complex.continuous_ofReal.comp (hbvel j)))
    change Continuous (fun y => (f y).scaledVertex (Sum.inr j) -
      ((f y).scale : ℂ) * ((f y).datum.boundaryVelocity j : ℂ)) at h
    have h' : Continuous (fun y => ((f y).datum.boundaryBase j : ℂ)) := by
      simpa only [scaledVertex, BoundaryClusterData.baseVertex, BoundaryClusterData.velocityVertex,
        BoundaryClusterData.doubledBase, BoundaryClusterData.doubledVelocity, add_sub_cancel_right] using h
    simpa only [Function.comp_def, Complex.ofReal_re] using Complex.continuous_re.comp h'
  apply IsEmbedding.subtypeVal.continuous_iff.mpr
  change Continuous (fun y => ((f y).datum, (f y).scale))
  apply Continuous.prodMk _ hr
  apply BoundaryClusterData.isEmbedding_coordinates.continuous_iff.mpr
  exact hcenter.prodMk ((continuous_pi hbase).prodMk ((continuous_pi hvel).prodMk
    ((continuous_pi hbbase).prodMk (continuous_pi hbvel))))

def rangeHomeomorph : BoundaryClusterDomain i a m S l u ≃ₜ
    Set.range (insertion : BoundaryClusterDomain i a m S l u → Compactification i m) := by
  let e := Equiv.ofInjective (insertion : BoundaryClusterDomain i a m S l u → Compactification i m)
    insertion_injective
  refine ⟨e, ?_, ?_⟩
  · exact continuous_insertion.subtype_mk _
  · apply continuous_of_continuous_insertion e.symm
    have heq : (fun y => (e.symm y).insertion) = Subtype.val := by
      funext y
      exact congrArg Subtype.val (e.apply_symm_apply y)
    rw [heq]
    exact continuous_subtype_val

/-- A real single-cluster insertion is a topological embedding through its boundary face. -/
theorem isEmbedding_insertion :
    IsEmbedding (insertion : BoundaryClusterDomain i a m S l u → Compactification i m) :=
  IsEmbedding.subtypeVal.comp rangeHomeomorph.isEmbedding

end EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryClusterDomain
