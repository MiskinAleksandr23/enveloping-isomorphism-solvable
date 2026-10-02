import EnvelopingIsomorphism.Deformation.Kontsevich.ForestShapeProjectionSmooth
import EnvelopingIsomorphism.Deformation.Kontsevich.ForestOrthantRealization
import EnvelopingIsomorphism.Deformation.Kontsevich.ForestPositiveForwardCoordinates

/-! Actual positive-locus forest coordinates in the native original real
configuration chart. Smoothness comes from affine/conjugate doubled points,
the marked-gap factory, and explicit free-coordinate and angle projections.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace EnvelopingIsomorphism.Deformation.Kontsevich.ForestPositiveChartSmooth

open Configuration ExtractedForestParameters ExtractedForestFrames ExtractedForestDRReferences
open ExtractedForestShapeCoordinates ForestOrthantCharts ForestOrthantRealization
open ForestShapeProjectionSmooth ForestMarkedFrames ComplexConjugate Set Topology Filter
open scoped Classical ContDiff NNReal

variable {n m : ℕ} (i : Fin (n + 1))


variable (x : Compactification i m)

def factoryInput (q : GraphForms.Coordinates n m) (v : tree i x) : ℂ := doubledRaw i q (lab i x v)

theorem contDiff_factoryInput {ν : ℕ∞ω} : ContDiff ℝ ν (factoryInput i x) := by
  apply contDiff_pi.mpr
  intro v
  exact contDiff_pi.mp (contDiff_doubledRaw i) (lab i x v)

theorem factoryInput_eq (q : GraphForms.CoordinateDomain n m) :
    factoryInput i x q.val = ExtractedForestOriginalDecode.input i x (toNormalized i q).val := by
  funext v
  exact congrFun (doubledRaw_eq i q) (lab i x v)

/-- The genuine marked radius/increment factory, extended to all original real coordinates. -/
def factory (q : GraphForms.Coordinates n m) : ForestParameterSpace.Ambient (tree i x) :=
  (ForestLeafRadii.fixLeaves (tree i x) (localRadii (tree i x) (frames i x) (factoryInput i x q)),
    increments (tree i x) (frames i x) (factoryInput i x q))

theorem factory_eq (q : GraphForms.CoordinateDomain n m) :
    factory i x q.val = ExtractedForestOriginalDecode.factoryParameters i x (toNormalized i q).val := by
  unfold factory ExtractedForestOriginalDecode.factoryParameters
  rw [factoryInput_eq]

/-- All smoothness orders, including analytic order, follow from actual positive marked gaps. -/
theorem contDiffAt_factory (q : GraphForms.Coordinates n m)
    (hq : factoryInput i x q ∈ PositiveGaps (tree i x) (frames i x)) {ν : ℕ∞ω} :
    ContDiffAt ℝ ν (factory i x) q := by
  apply ContDiffAt.prodMk
  · apply contDiffAt_pi.mpr
    intro v
    unfold ForestLeafRadii.fixLeaves
    by_cases hv : IsMax v
    · simp only [if_pos hv]
      exact contDiffAt_const
    · simp only [if_neg hv]
      exact (contDiffAt_pi.mp (ForestMarkedFrames.contDiffAt_localRadii (tree i x) (frames i x)
        _ hq) v).comp q (contDiff_factoryInput i x).contDiffAt
  · exact (ForestMarkedFrames.contDiffAt_increments (tree i x) (frames i x) _ hq).comp q
      (contDiff_factoryInput i x).contDiffAt

def radialRaw (p : ForestParameterSpace.Ambient (tree i x)) (j : Fin (R i x)) : ℝ :=
  p.1 (((Fintype.equivFin (ReflectedRadiusCoordinates.Orbit (tree i x) (reflection i x)
    (reflection_reflection i x))).symm j).out).val

def phaseRaw (p : ForestParameterSpace.Ambient (tree i x)) (j : Fin (C i x)) : ℂ :=
  ForestShapeProjectionSmooth.circleRaw (tree i x) (reflection i x) (frames i x) (pairedMarks i x)
    p.2 ((Fintype.equivFin _).symm j)

def freeRealRaw (p : ForestParameterSpace.Ambient (tree i x)) (j : Fin (Q i x)) : ℝ :=
  ForestShapeProjectionSmooth.realRaw (tree i x) (reflection i x) (reflection_reflection i x)
    (frames i x) (pairedMarks i x) (fixedMarks i x) p.2 ((Fintype.equivFin _).symm j)

/-- The actual free inverse in ambient real variables; each angle uses its prescribed open branch. -/
def freeInverse (p : ForestParameterSpace.Ambient (tree i x)) : ForestOrthantRealization.Ambient i x :=
  (radialRaw i x p, fun j => Sum.elim
    (fun a => angleInverseRaw ((centerModel i x).2.1 a) (phaseRaw i x p a))
    (freeRealRaw i x p) (finSumFinEquiv.symm j))

def AngleBranch (p : ForestParameterSpace.Ambient (tree i x)) : Prop :=
  ∀ j : Fin (C i x), ((centerModel i x).2.1 j : ℂ)⁻¹ * phaseRaw i x p j ∈ Complex.slitPlane

theorem contDiffAt_freeInverse (p : ForestParameterSpace.Ambient (tree i x))
    (hp : AngleBranch i x p) {ν : ℕ∞ω} : ContDiffAt ℝ ν (freeInverse i x) p := by
  apply ContDiffAt.prodMk
  · apply contDiffAt_pi.mpr
    intro j
    unfold radialRaw
    fun_prop
  · apply contDiffAt_pi.mpr
    intro j
    change ContDiffAt ℝ ν (fun p => Sum.elim
      (fun a => angleInverseRaw ((centerModel i x).2.1 a) (phaseRaw i x p a))
      (freeRealRaw i x p) (finSumFinEquiv.symm j)) p
    cases h : finSumFinEquiv.symm j with
    | inl a =>
      simp only [Sum.elim_inl]
      apply (contDiffAt_angleInverseRaw _ _ (hp a)).comp p
      exact (contDiff_pi.mp (contDiff_circleRaw (tree i x) (reflection i x) (frames i x)
        (pairedMarks i x)) ((Fintype.equivFin _).symm a)).contDiffAt.comp p contDiffAt_snd
    | inr a =>
      simp only [Sum.elim_inr]
      exact (contDiff_pi.mp (contDiff_realRaw (tree i x) (reflection i x) (reflection_reflection i x)
        (frames i x) (pairedMarks i x) (fixedMarks i x)) ((Fintype.equivFin _).symm a)).contDiffAt.comp p contDiffAt_snd

def inverseCoordinates (q : GraphForms.Coordinates n m) : ForestOrthantRealization.Ambient i x :=
  freeInverse i x (factory i x q)

theorem contDiffAt_inverseCoordinates (q : GraphForms.Coordinates n m)
    (hg : factoryInput i x q ∈ PositiveGaps (tree i x) (frames i x))
    (ha : AngleBranch i x (factory i x q)) {ν : ℕ∞ω} : ContDiffAt ℝ ν (inverseCoordinates i x) q :=
  (contDiffAt_freeInverse i x _ ha).comp q (contDiffAt_factory i x q hg)

theorem piCongrLeft_const_apply {A B E : Type*} [TopologicalSpace E]
    (e : A ≃ B) (f : A → E) (j : B) :
    Homeomorph.piCongrLeft (Y := fun _ : B => E) e f j = f (e.symm j) := by
  obtain ⟨a, rfl⟩ := e.surjective j
  rw [Homeomorph.piCongrLeft_apply_apply, Equiv.symm_apply_apply]

theorem equiv_piCongrLeft_const_apply {A B E : Type*} (e : A ≃ B) (f : A → E) (j : B) :
    Equiv.piCongrLeft (fun _ : B => E) e f j = f (e.symm j) := by
  obtain ⟨a, rfl⟩ := e.surjective j
  rw [Equiv.piCongrLeft_apply_apply, Equiv.symm_apply_apply]

theorem combineReal_apply (q : (Fin (C i x) → ℝ) × (Fin (Q i x) → ℝ)) (j : Fin (C i x + Q i x)) :
    combineReal i x q j = Sum.elim q.1 q.2 (finSumFinEquiv.symm j) :=
  piCongrLeft_const_apply finSumFinEquiv _ _

theorem radialRaw_eq (p : ForestChartOpenImage.ParameterSpace i x) (j : Fin (R i x)) :
    radialRaw i x p.val j = ((ExtractedForestShapeCoordinates.coordinatesHomeomorph i x p).1 j : ℝ) := by
  obtain ⟨z, rfl⟩ := (ExtractedForestShapeCoordinates.coordinatesHomeomorph i x).symm.surjective p
  rw [Homeomorph.apply_symm_apply]
  let o := (Fintype.equivFin (ReflectedRadiusCoordinates.Orbit (tree i x) (reflection i x)
    (reflection_reflection i x))).symm j
  change (if hu : ReflectedRadiusCoordinates.Active (tree i x) o.out.val then
    (z.1 (Fintype.equivFin _ (ReflectedRadiusCoordinates.orbitClass (tree i x) (reflection i x)
      (reflection_reflection i x) ⟨o.out.val, hu⟩)) : ℝ) else 1) = _
  rw [dif_pos o.out.property]
  have ho : ReflectedRadiusCoordinates.orbitClass (tree i x) (reflection i x)
      (reflection_reflection i x) o.out = o := Quotient.out_eq o
  rw [ho]
  exact congrArg (fun j => (z.1 j : ℝ)) (Equiv.apply_symm_apply _ j)

theorem phaseRaw_eq (p : ForestChartOpenImage.ParameterSpace i x) (j : Fin (C i x)) :
    phaseRaw i x p.val j = ((ExtractedForestShapeCoordinates.coordinatesHomeomorph i x p).2.1 j : ℂ) := by
  obtain ⟨z, rfl⟩ := (ExtractedForestShapeCoordinates.coordinatesHomeomorph i x).symm.surjective p
  rw [Homeomorph.apply_symm_apply]
  let s := (ForestShapeCoordinates.shapeRealHomeomorph (tree i x) (reflection i x) (reflection_reflection i x)
    (frames i x) (pairedMarks i x) (fixedMarks i x)).symm
      (fun v => z.2.1 (Fintype.equivFin _ v), fun v => z.2.2 (Fintype.equivFin _ v))
  have h := circleRaw_eq (tree i x) (reflection i x) (reflection_reflection i x) (frames i x)
    (pairedMarks i x) (fixedMarks i x) s ((Fintype.equivFin _).symm j)
  have hs : ((ExtractedForestShapeCoordinates.coordinatesHomeomorph i x).symm z).val.2 = s.val := by rfl
  unfold phaseRaw
  rw [hs]
  simpa only [s, Homeomorph.apply_symm_apply, Equiv.apply_symm_apply] using h

theorem freeRealRaw_eq (p : ForestChartOpenImage.ParameterSpace i x) (j : Fin (Q i x)) :
    freeRealRaw i x p.val j = (ExtractedForestShapeCoordinates.coordinatesHomeomorph i x p).2.2 j := by
  obtain ⟨z, rfl⟩ := (ExtractedForestShapeCoordinates.coordinatesHomeomorph i x).symm.surjective p
  rw [Homeomorph.apply_symm_apply]
  let s := (ForestShapeCoordinates.shapeRealHomeomorph (tree i x) (reflection i x) (reflection_reflection i x)
    (frames i x) (pairedMarks i x) (fixedMarks i x)).symm
      (fun v => z.2.1 (Fintype.equivFin _ v), fun v => z.2.2 (Fintype.equivFin _ v))
  have h := congrFun (realRaw_eq (tree i x) (reflection i x) (reflection_reflection i x) (frames i x)
    (pairedMarks i x) (fixedMarks i x) s) ((Fintype.equivFin _).symm j)
  have hs : ((ExtractedForestShapeCoordinates.coordinatesHomeomorph i x).symm z).val.2 = s.val := by rfl
  unfold freeRealRaw
  rw [hs]
  simpa only [s, Homeomorph.apply_symm_apply, Equiv.apply_symm_apply] using h

/-- Restriction of the explicit ambient formula is the actual free-coordinate inverse. -/
theorem freeInverse_eq (p : ForestChartOpenImage.ParameterSpace i x) :
    freeInverse i x p.val = includeOrthant i x ((splitHomeomorph i x).symm
      ((angles i x).symm (ExtractedForestShapeCoordinates.coordinatesHomeomorph i x p))) := by
  apply Prod.ext
  · funext j
    exact radialRaw_eq i x p j
  · funext j
    change _ = combineReal i x (((angles i x).symm (ExtractedForestShapeCoordinates.coordinatesHomeomorph i x p)).2) j
    rw [combineReal_apply]
    change Sum.elim
      (fun a => angleInverseRaw ((centerModel i x).2.1 a) (phaseRaw i x p.val a))
      (freeRealRaw i x p.val) (finSumFinEquiv.symm j) =
      Sum.elim
      (fun a => (angleChart ((centerModel i x).2.1 a)).symm
        ((ExtractedForestShapeCoordinates.coordinatesHomeomorph i x p).2.1 a))
      ((ExtractedForestShapeCoordinates.coordinatesHomeomorph i x p).2.2) (finSumFinEquiv.symm j)
    cases h : finSumFinEquiv.symm j with
    | inl a => simp only [Sum.elim_inl, phaseRaw_eq, angleInverseRaw_eq]
    | inr a => exact freeRealRaw_eq i x p a

theorem angleBranch_of_angles_target (p : ForestChartOpenImage.ParameterSpace i x)
    (hp : ExtractedForestShapeCoordinates.coordinatesHomeomorph i x p ∈ (angles i x).target) :
    AngleBranch i x p.val := by
  intro j
  rw [phaseRaw_eq]
  exact angleInverseRaw_slit _ _ (hp.2.1 j (mem_univ j))

theorem parameterChart_inverse_val (y : Compactification i m)
    (hy : y ∈ ForestChartOpenImage.target i x) :
    ((ForestChartOpenImage.parameterChart i x).symm y).val = ForestChartOpenImage.decoder i x y := by
  change (ForestChartOpenImage.inverseTotal i x y).val.val = _
  rw [ForestChartOpenImage.inverseTotal_of_mem i x y hy]
  rfl

theorem original_mem_referenceRegion (q : GraphForms.CoordinateDomain n m)
    (hy : originalEmbedding i q ∈ (ForestOrthantCharts.chart i x).target) :
    directionRatioCoordinates (toNormalized i q).val ∈ ForestDRInverse.Region (tree i x)
      (lab i x) (frames i x) (ExtractedForestDRReferences.reference i x) := by
  have hp := hy.1.1.1
  rw [ForestChartOpenImage.parameterChart_target] at hp
  exact hp.1

theorem original_inverse_factory (q : GraphForms.CoordinateDomain n m)
    (hy : originalEmbedding i q ∈ (ForestOrthantCharts.chart i x).target) :
    ((ForestChartOpenImage.parameterChart i x).symm (originalEmbedding i q)).val = factory i x q.val := by
  have hp := hy.1.1.1
  rw [ForestChartOpenImage.parameterChart_target] at hp
  rw [parameterChart_inverse_val i x _ hp, factory_eq]
  exact ExtractedForestOriginalDecode.decode_eq_factory i x (toNormalized i q).val
    (original_mem_referenceRegion i x q hy)

/-- The inverse chart is represented by the explicit marked factory and free-coordinate formula. -/
theorem inverseCoordinates_eq_chart_symm (q : GraphForms.CoordinateDomain n m)
    (hy : originalEmbedding i q ∈ (ForestOrthantCharts.chart i x).target) :
    inverseCoordinates i x q.val = includeOrthant i x ((ForestOrthantCharts.chart i x).symm (originalEmbedding i q)) := by
  unfold inverseCoordinates
  rw [← original_inverse_factory i x q hy, freeInverse_eq]
  rfl

theorem positiveGaps_of_mem_target (q : GraphForms.CoordinateDomain n m)
    (hy : originalEmbedding i q ∈ (ForestOrthantCharts.chart i x).target) :
    factoryInput i x q.val ∈ PositiveGaps (tree i x) (frames i x) := by
  rw [factoryInput_eq]
  exact ExtractedForestOriginalDecode.positiveGaps i x (toNormalized i q).val
    (original_mem_referenceRegion i x q hy)

theorem angleBranch_of_mem_target (q : GraphForms.CoordinateDomain n m)
    (hy : originalEmbedding i q ∈ (ForestOrthantCharts.chart i x).target) :
    AngleBranch i x (factory i x q.val) := by
  rw [← original_inverse_factory i x q hy]
  exact angleBranch_of_angles_target i x _ hy.1.2

/-- At every actual positive original point in the chart target, its literal
inverse coordinate formula is real smooth of every order, including analytic order. -/
theorem contDiffAt_inverseCoordinates_original (q : GraphForms.CoordinateDomain n m)
    (hy : originalEmbedding i q ∈ (ForestOrthantCharts.chart i x).target) {ν : ℕ∞ω} :
    ContDiffAt ℝ ν (inverseCoordinates i x) q.val :=
  contDiffAt_inverseCoordinates i x q.val (positiveGaps_of_mem_target i x q hy)
    (angleBranch_of_mem_target i x q hy)

def ofAmbient (z : ForestOrthantRealization.Ambient i x) : ForestOrthantCharts.Model i x :=
  (fun j => (z.1 j).toNNReal, z.2)

theorem continuous_ofAmbient : Continuous (ofAmbient i x) := by
  apply Continuous.prodMk
  · apply continuous_pi
    intro j
    exact continuous_real_toNNReal.comp ((continuous_apply j).comp continuous_fst)
  · exact continuous_snd

@[simp] theorem ofAmbient_includeOrthant (z : ForestOrthantCharts.Model i x) :
    ofAmbient i x (includeOrthant i x z) = z := by
  ext j <;> simp [ofAmbient, includeOrthant]

theorem includeOrthant_ofAmbient (z : ForestOrthantRealization.Ambient i x) (hz : ∀ j, 0 ≤ z.1 j) :
    includeOrthant i x (ofAmbient i x z) = z := by
  apply Prod.ext
  · funext j
    change ((z.1 j).toNNReal : ℝ) = z.1 j
    exact max_eq_left (hz j)
  · rfl

/-- The actual positive part of the orthant chart is an open set in its full real ambient space. -/
def Source : Set (ForestOrthantRealization.Ambient i x) :=
  {z | (∀ j, 0 < z.1 j) ∧ ofAmbient i x z ∈ (ForestOrthantCharts.chart i x).source}

theorem isOpen_Source : IsOpen (Source i x) := by
  change IsOpen ({z : ForestOrthantRealization.Ambient i x | ∀ j, 0 < z.1 j} ∩
    (ofAmbient i x) ⁻¹' (ForestOrthantCharts.chart i x).source)
  apply IsOpen.inter
  · simp only [setOf_forall]
    apply isOpen_iInter_of_finite
    intro j
    exact isOpen_lt continuous_const ((continuous_apply j).comp continuous_fst)
  · exact (ForestOrthantCharts.chart i x).open_source.preimage (continuous_ofAmbient i x)

theorem realization_pos (z : ForestOrthantRealization.Ambient i x) (hz : z ∈ Source i x) (v : tree i x) :
    0 < (realization i x z).1 v := by
  change 0 < radiusArray i x z v
  unfold radiusArray
  split_ifs
  · exact hz.1 _
  · exact zero_lt_one

def sourceCorner (z : ForestOrthantRealization.Ambient i x) (hz : z ∈ Source i x) :
    ForestChartConfigurations.CornerDomain (ExtractedForestChildShapes.shapeData i x) :=
  ForestChartOpenImage.toCorner i x (ForestOrthantRealization.sourcePoint i x (ofAmbient i x z) hz.2)

theorem sourceCorner_val (z : ForestOrthantRealization.Ambient i x) (hz : z ∈ Source i x) :
    (sourceCorner i x z hz).val = realization i x z := by
  change (parameterPoint i x (ofAmbient i x z)).val = _
  unfold ForestOrthantRealization.parameterPoint
  rw [← realization_eq_model, includeOrthant_ofAmbient i x z (fun j => (hz.1 j).le)]

theorem sourceCorner_pos (z : ForestOrthantRealization.Ambient i x) (hz : z ∈ Source i x) (v : tree i x) :
    0 < (sourceCorner i x z hz).val.1 v := by
  rw [sourceCorner_val]
  exact realization_pos i x z hz v

/-- The native positive configuration whose coordinates the smooth formula normalizes. -/
def positiveConfiguration (z : ForestOrthantRealization.Ambient i x) (hz : z ∈ Source i x) :
    Configuration (n + 1) m :=
  ForestChartConfigurations.configuration (ExtractedForestChildShapes.shapeData i x)
    (sourceCorner i x z hz).val (sourceCorner i x z hz).property.2.2
    (fun v _ => sourceCorner_pos i x z hz v)
    (sourceCorner i x z hz).property.1.2.2.1 (sourceCorner i x z hz).property.2.1

theorem positiveConfiguration_doubledPoint (z : ForestOrthantRealization.Ambient i x) (hz : z ∈ Source i x)
    (v : DoubledLabel (n + 1) m) :
    (positiveConfiguration i x z hz).doubledPoint v = leafPositions i x z v := by
  have h := ForestChartConfigurations.configuration_doubledPoint (ExtractedForestChildShapes.shapeData i x)
    (sourceCorner i x z hz).val (sourceCorner i x z hz).property.2.2
    (fun u _ => sourceCorner_pos i x z hz u)
    (sourceCorner i x z hz).property.1.2.2.1 (sourceCorner i x z hz).property.2.1 v
  exact h.trans (congrArg (fun p => ForestChartConfigurations.positions
    (ExtractedForestChildShapes.shapeData i x) p v) (sourceCorner_val i x z hz))

theorem anchorPoint_im_pos (z : ForestOrthantRealization.Ambient i x) (hz : z ∈ Source i x) :
    0 < (anchorPoint i x z).im := by
  have h := (positiveConfiguration i x z hz).interior i |>.im_pos
  have hp := positiveConfiguration_doubledPoint i x z hz (Sum.inl (Sum.inl i))
  change ((positiveConfiguration i x z hz).interior i : ℂ) = anchorPoint i x z at hp
  change 0 < (((positiveConfiguration i x z hz).interior i : ℂ)).im at h
  rwa [hp] at h

theorem forwardCoordinates_eq_normalized (z : ForestOrthantRealization.Ambient i x) (hz : z ∈ Source i x) :
    forwardCoordinates i x z = fromNormalized i (Configuration.normalized i (positiveConfiguration i x z hz)) := by
  have hp (j : Fin (n + 1)) : ((positiveConfiguration i x z hz).interior j : ℂ) =
      leafPositions i x z (Sum.inl (Sum.inl j)) :=
    positiveConfiguration_doubledPoint i x z hz (Sum.inl (Sum.inl j))
  have hb (j : Fin m) : (positiveConfiguration i x z hz).boundary j =
      (leafPositions i x z (Sum.inl (Sum.inr j))).re := by
    simpa only [Configuration.doubledPoint, Configuration.vertexPoint, Sum.elim_inl, Sum.elim_inr,
      Complex.ofReal_re] using congrArg Complex.re (positiveConfiguration_doubledPoint i x z hz (Sum.inl (Sum.inr j)))
  apply Prod.ext
  · funext j
    change _ = ((Configuration.normalize i (positiveConfiguration i x z hz)).interior (Equiv.swap 0 i j.succ) : ℂ)
    rw [Configuration.normalize_interior_complex]
    change _ = (((positiveConfiguration i x z hz).interior (Equiv.swap 0 i j.succ) : ℂ) -
      ((((positiveConfiguration i x z hz).interior i : ℂ)).re : ℂ)) /
      ((((positiveConfiguration i x z hz).interior i : ℂ)).im : ℂ)
    rw [hp, hp]
    rfl
  · funext j
    change _ = (Configuration.normalize i (positiveConfiguration i x z hz)).boundary j
    rw [Configuration.normalize_boundary_real]
    change _ = ((positiveConfiguration i x z hz).boundary j -
      (((positiveConfiguration i x z hz).interior i : ℂ)).re) /
      (((positiveConfiguration i x z hz).interior i : ℂ)).im
    rw [hb, hp]
    rfl

theorem forwardCoordinates_admissible (z : ForestOrthantRealization.Ambient i x) (hz : z ∈ Source i x) :
    GraphForms.Admissible (forwardCoordinates i x z) := by
  rw [forwardCoordinates_eq_normalized i x z hz]
  exact fromNormalized_admissible i _

/-- On positive real parameters the explicit coordinate formula is exactly the actual compactification chart. -/
theorem originalEmbedding_forwardCoordinates (z : ForestOrthantRealization.Ambient i x) (hz : z ∈ Source i x) :
    originalEmbedding i ⟨forwardCoordinates i x z, forwardCoordinates_admissible i x z hz⟩ =
      ForestOrthantCharts.chart i x (ofAmbient i x z) := by
  have hc : toNormalized i ⟨forwardCoordinates i x z, forwardCoordinates_admissible i x z hz⟩ =
      Configuration.normalized i (positiveConfiguration i x z hz) := by
    simp only [forwardCoordinates_eq_normalized i x z hz, toNormalized_fromNormalized]
  unfold originalEmbedding
  rw [hc, chart_eq_forward i x _ hz.2]
  symm
  exact ForestChartConfigurations.compactificationInsertion_eq_embedding
    (ExtractedForestChildShapes.shapeData i x) i (sourceCorner i x z hz)
      (fun v _ => sourceCorner_pos i x z hz v)

theorem forwardCoordinates_mem_target (z : ForestOrthantRealization.Ambient i x) (hz : z ∈ Source i x) :
    originalEmbedding i ⟨forwardCoordinates i x z, forwardCoordinates_admissible i x z hz⟩ ∈
      (ForestOrthantCharts.chart i x).target := by
  rw [originalEmbedding_forwardCoordinates i x z hz]
  exact (ForestOrthantCharts.chart i x).map_source hz.2

theorem contDiffAt_forwardCoordinates_source (z : ForestOrthantRealization.Ambient i x)
    (hz : z ∈ Source i x) {ν : ℕ∞ω} : ContDiffAt ℝ ν (forwardCoordinates i x) z :=
  contDiffAt_forwardCoordinates i x z (anchorPoint_im_pos i x z hz).ne'

theorem inverse_forwardCoordinates (z : ForestOrthantRealization.Ambient i x) (hz : z ∈ Source i x) :
    inverseCoordinates i x (forwardCoordinates i x z) = z := by
  rw [inverseCoordinates_eq_chart_symm i x _ (forwardCoordinates_mem_target i x z hz),
    originalEmbedding_forwardCoordinates i x z hz, (ForestOrthantCharts.chart i x).left_inv hz.2,
    includeOrthant_ofAmbient i x z (fun j => (hz.1 j).le)]

theorem inverseCoordinates_radius_pos (q : GraphForms.CoordinateDomain n m)
    (hy : originalEmbedding i q ∈ (ForestOrthantCharts.chart i x).target) (j : Fin (R i x)) :
    0 < (inverseCoordinates i x q.val).1 j := by
  let o := (Fintype.equivFin (ReflectedRadiusCoordinates.Orbit (tree i x) (reflection i x)
    (reflection_reflection i x))).symm j
  change 0 < ForestLeafRadii.fixLeaves (tree i x)
    (localRadii (tree i x) (frames i x) (factoryInput i x q.val)) o.out.val
  rw [ForestLeafRadii.fixLeaves, if_neg o.out.property.2]
  exact localRadii_pos (tree i x) (frames i x) _ (positiveGaps_of_mem_target i x q hy) o.out.val

theorem inverseCoordinates_mem_Source (q : GraphForms.CoordinateDomain n m)
    (hy : originalEmbedding i q ∈ (ForestOrthantCharts.chart i x).target) :
    inverseCoordinates i x q.val ∈ Source i x := by
  refine ⟨inverseCoordinates_radius_pos i x q hy, ?_⟩
  rw [inverseCoordinates_eq_chart_symm i x q hy, ofAmbient_includeOrthant]
  exact (ForestOrthantCharts.chart i x).map_target hy

theorem originalEmbedding_injective : Function.Injective (originalEmbedding (m := m) i) := by
  intro q r h
  have hc := (isEmbedding_compactificationEmbedding i).injective h
  apply Subtype.ext
  exact (fromNormalized_toNormalized i q).symm.trans ((congrArg (fromNormalized i) hc).trans (fromNormalized_toNormalized i r))

theorem forward_inverseCoordinates (q : GraphForms.CoordinateDomain n m)
    (hy : originalEmbedding i q ∈ (ForestOrthantCharts.chart i x).target) :
    forwardCoordinates i x (inverseCoordinates i x q.val) = q.val := by
  have hs := inverseCoordinates_mem_Source i x q hy
  have h := originalEmbedding_forwardCoordinates i x _ hs
  have hr : ForestOrthantCharts.chart i x (ofAmbient i x (inverseCoordinates i x q.val)) = originalEmbedding i q := by
    rw [inverseCoordinates_eq_chart_symm i x q hy, ofAmbient_includeOrthant,
      (ForestOrthantCharts.chart i x).right_inv hy]
  exact congrArg Subtype.val (originalEmbedding_injective i (h.trans hr))

def Target : Set (GraphForms.Coordinates n m) :=
  Subtype.val '' {q : GraphForms.CoordinateDomain n m | originalEmbedding i q ∈ (ForestOrthantCharts.chart i x).target}

theorem isOpen_Target : IsOpen (Target i x) :=
  (GraphForms.isOpen_admissibleSet n m).isOpenMap_subtype_val _
    ((ForestOrthantCharts.chart i x).open_target.preimage (continuous_originalEmbedding i))

theorem forwardCoordinates_mem_Target (z : ForestOrthantRealization.Ambient i x) (hz : z ∈ Source i x) :
    forwardCoordinates i x z ∈ Target i x :=
  ⟨⟨forwardCoordinates i x z, forwardCoordinates_admissible i x z hz⟩, forwardCoordinates_mem_target i x z hz, rfl⟩

theorem contDiffAt_inverseCoordinates_target (q : GraphForms.Coordinates n m) (hq : q ∈ Target i x)
    {ν : ℕ∞ω} : ContDiffAt ℝ ν (inverseCoordinates i x) q := by
  obtain ⟨q, hq, rfl⟩ := hq
  exact contDiffAt_inverseCoordinates_original i x q hq

theorem forward_inverseCoordinates_target (q : GraphForms.Coordinates n m) (hq : q ∈ Target i x) :
    forwardCoordinates i x (inverseCoordinates i x q) = q := by
  obtain ⟨q, hq, rfl⟩ := hq
  exact forward_inverseCoordinates i x q hq

theorem inverseCoordinates_mapsTo : MapsTo (inverseCoordinates i x) (Target i x) (Source i x) := by
  rintro q ⟨q, hq, rfl⟩
  exact inverseCoordinates_mem_Source i x q hq

/-- Equality of the actual positive coordinate image with the original chart target. -/
theorem forwardCoordinates_image : forwardCoordinates i x '' Source i x = Target i x := by
  apply Subset.antisymm
  · rintro q ⟨z, hz, rfl⟩
    exact forwardCoordinates_mem_Target i x z hz
  · intro q hq
    exact ⟨inverseCoordinates i x q, inverseCoordinates_mapsTo i x hq,
      forward_inverseCoordinates_target i x q hq⟩

theorem forwardCoordinates_injOn : InjOn (forwardCoordinates i x) (Source i x) := by
  intro z hz w hw h
  calc
    z = inverseCoordinates i x (forwardCoordinates i x z) := (inverse_forwardCoordinates i x z hz).symm
    _ = inverseCoordinates i x (forwardCoordinates i x w) := congrArg _ h
    _ = w := inverse_forwardCoordinates i x w hw

/-- A native open partial homeomorphism of real vector spaces whose two maps
were independently proved smooth by their actual construction formulas. -/
def positiveChart : OpenPartialHomeomorph (ForestOrthantRealization.Ambient i x) (GraphForms.Coordinates n m) where
  toFun := forwardCoordinates i x
  invFun := inverseCoordinates i x
  source := Source i x
  target := Target i x
  map_source' := forwardCoordinates_mem_Target i x
  map_target' := inverseCoordinates_mapsTo i x
  left_inv' := inverse_forwardCoordinates i x
  right_inv' := forward_inverseCoordinates_target i x
  continuousOn_toFun := fun z hz => (contDiffAt_forwardCoordinates_source (ν := 1) i x z hz).continuousAt.continuousWithinAt
  continuousOn_invFun := fun q hq => (contDiffAt_inverseCoordinates_target (ν := 1) i x q hq).continuousAt.continuousWithinAt
  open_source := isOpen_Source i x
  open_target := isOpen_Target i x

theorem fderiv_inverse_comp_forward (z : ForestOrthantRealization.Ambient i x) (hz : z ∈ Source i x) :
    (fderiv ℝ (inverseCoordinates i x) (forwardCoordinates i x z)).comp
      (fderiv ℝ (forwardCoordinates i x) z) = ContinuousLinearMap.id ℝ (ForestOrthantRealization.Ambient i x) := by
  have hf := (contDiffAt_forwardCoordinates_source (ν := 1) i x z hz).differentiableAt (by norm_num)
  have hg := (contDiffAt_inverseCoordinates_target (ν := 1) i x _ (forwardCoordinates_mem_Target i x z hz)).differentiableAt (by norm_num)
  have he : (inverseCoordinates i x ∘ forwardCoordinates i x) =ᶠ[𝓝 z] id := by
    filter_upwards [(isOpen_Source i x).mem_nhds hz] with w hw
    exact inverse_forwardCoordinates i x w hw
  exact ((hg.hasFDerivAt.comp z hf.hasFDerivAt).congr_of_eventuallyEq he.symm).unique (hasFDerivAt_id z)

theorem fderiv_forward_comp_inverse (z : ForestOrthantRealization.Ambient i x) (hz : z ∈ Source i x) :
    (fderiv ℝ (forwardCoordinates i x) z).comp
      (fderiv ℝ (inverseCoordinates i x) (forwardCoordinates i x z)) =
        ContinuousLinearMap.id ℝ (GraphForms.Coordinates n m) := by
  have hf : DifferentiableAt ℝ (forwardCoordinates i x) (inverseCoordinates i x (forwardCoordinates i x z)) := by
    rw [inverse_forwardCoordinates i x z hz]
    exact (contDiffAt_forwardCoordinates_source (ν := 1) i x z hz).differentiableAt (by norm_num)
  have hg := (contDiffAt_inverseCoordinates_target (ν := 1) i x _ (forwardCoordinates_mem_Target i x z hz)).differentiableAt (by norm_num)
  have he : (forwardCoordinates i x ∘ inverseCoordinates i x) =ᶠ[𝓝 (forwardCoordinates i x z)] id := by
    filter_upwards [(isOpen_Target i x).mem_nhds (forwardCoordinates_mem_Target i x z hz)] with q hq
    exact forward_inverseCoordinates_target i x q hq
  have h := ((hf.hasFDerivAt.comp (forwardCoordinates i x z) hg.hasFDerivAt).congr_of_eventuallyEq he.symm).unique
    (hasFDerivAt_id (forwardCoordinates i x z))
  rwa [inverse_forwardCoordinates i x z hz] at h

/-- The actual real derivative is a continuous linear equivalence, by the two
C1 chain rules and the proved local inverse identities. No dimension premise occurs. -/
def derivativeLinearEquiv (z : ForestOrthantRealization.Ambient i x) (hz : z ∈ Source i x) :
    ForestOrthantRealization.Ambient i x ≃L[ℝ] GraphForms.Coordinates n m where
  toLinearEquiv :=
    { toFun := fderiv ℝ (forwardCoordinates i x) z
      invFun := fderiv ℝ (inverseCoordinates i x) (forwardCoordinates i x z)
      left_inv := by
        intro v
        exact congrArg (fun L : ForestOrthantRealization.Ambient i x →L[ℝ] ForestOrthantRealization.Ambient i x => L v)
          (fderiv_inverse_comp_forward i x z hz)
      right_inv := by
        intro v
        exact congrArg (fun L : GraphForms.Coordinates n m →L[ℝ] GraphForms.Coordinates n m => L v)
          (fderiv_forward_comp_inverse i x z hz)
      map_add' := (fderiv ℝ (forwardCoordinates i x) z).map_add
      map_smul' := (fderiv ℝ (forwardCoordinates i x) z).map_smul }
  continuous_toFun := (fderiv ℝ (forwardCoordinates i x) z).continuous
  continuous_invFun := (fderiv ℝ (inverseCoordinates i x) (forwardCoordinates i x z)).continuous

@[simp] theorem derivativeLinearEquiv_toContinuousLinearMap (z : ForestOrthantRealization.Ambient i x)
    (hz : z ∈ Source i x) : (derivativeLinearEquiv i x z hz).toContinuousLinearMap =
      fderiv ℝ (forwardCoordinates i x) z := rfl

@[simp] theorem derivativeLinearEquiv_symm_toContinuousLinearMap (z : ForestOrthantRealization.Ambient i x)
    (hz : z ∈ Source i x) : (derivativeLinearEquiv i x z hz).symm.toContinuousLinearMap =
      fderiv ℝ (inverseCoordinates i x) (forwardCoordinates i x z) := rfl

theorem finrank_eq (z : ForestOrthantRealization.Ambient i x) (hz : z ∈ Source i x) :
    Module.finrank ℝ (ForestOrthantRealization.Ambient i x) = Module.finrank ℝ (GraphForms.Coordinates n m) :=
  (derivativeLinearEquiv i x z hz).toLinearEquiv.finrank_eq

end EnvelopingIsomorphism.Deformation.Kontsevich.ForestPositiveChartSmooth
