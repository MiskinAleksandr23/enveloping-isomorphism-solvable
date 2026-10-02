import EnvelopingIsomorphism.Deformation.Kontsevich.ForestOrthantRealization
import EnvelopingIsomorphism.Deformation.Kontsevich.ForestGraphTopForms
import EnvelopingIsomorphism.Deformation.Kontsevich.VariableAffineForms

/-! Actual graph forms pulled back to the smooth free orthant realization. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Kontsevich.ForestOrthantGraphForms

open ForestOrthantRealization ExtractedForestParameters ExtractedForestFrames ExtractedForestChildShapes
open ForestGraphForms ForestGraphTopForms ContinuousAlternatingMap ComplexConjugate
open scoped Classical Topology ContDiff

section Projection

variable (T : RootedTree) [Fintype T] (σ : T ≃o T) (hσ : Function.Involutive σ)

def reflectionCLM : ForestDirectionRatioCoordinates.Parameters T →L[ℝ] ForestDirectionRatioCoordinates.Parameters T :=
  ((ContinuousLinearMap.pi fun v => ContinuousLinearMap.proj (σ v)).comp
    (ContinuousLinearMap.fst ℝ (T → ℝ) (T → ℂ))).prod
  ((ContinuousLinearMap.pi fun v => Complex.conjCLE.toContinuousLinearMap.comp (ContinuousLinearMap.proj (σ v))).comp
    (ContinuousLinearMap.snd ℝ (T → ℝ) (T → ℂ)))

def averageCLM : ForestDirectionRatioCoordinates.Parameters T →L[ℝ] ForestDirectionRatioCoordinates.Parameters T :=
  (1 / 2 : ℝ) • (ContinuousLinearMap.id ℝ _ + reflectionCLM T σ)

omit [Fintype T] in
include hσ in
theorem average_mem (p : ForestDirectionRatioCoordinates.Parameters T) :
    averageCLM T σ p ∈ ForestMarkedFrameReflection.parameterSubmodule T σ := by
  constructor
  · intro v
    change (1 / 2 : ℝ) • (p.1 (σ v) + p.1 (σ (σ v))) = (1 / 2 : ℝ) • (p.1 v + p.1 (σ v))
    rw [hσ v, add_comm]
  · intro v
    change (1 / 2 : ℝ) • (p.2 (σ v) + conj (p.2 (σ (σ v)))) =
      conj ((1 / 2 : ℝ) • (p.2 v + conj (p.2 (σ v))))
    simp only [hσ v, Complex.real_smul, map_mul, Complex.conj_ofReal, map_add, Complex.conj_conj]
    rw [add_comm]

def projection : ForestDirectionRatioCoordinates.Parameters T →L[ℝ]
    ForestMarkedFrameReflection.parameterSubmodule T σ :=
  (averageCLM T σ).codRestrict _ (average_mem T σ hσ)

omit [Fintype T] in
theorem projection_eq (p : ForestDirectionRatioCoordinates.Parameters T)
    (hp : p ∈ ForestMarkedFrameReflection.parameterSubmodule T σ) :
    (projection T σ hσ p).val = p := by
  apply Prod.ext
  · funext v
    change (1 / 2 : ℝ) * (p.1 v + p.1 (σ v)) = p.1 v
    rw [hp.1 v]
    ring
  · funext v
    change (1 / 2 : ℝ) • (p.2 v + conj (p.2 (σ v))) = p.2 v
    rw [hp.2 v, Complex.conj_conj, ← two_smul ℝ, smul_smul]
    norm_num

end Projection

variable {n m : ℕ} (i : Fin n) (x : Compactification i m)

def reflectedRealization (z : ForestOrthantRealization.Ambient i x) : ParameterSpace (shapeData i x) :=
  projection (tree i x) (reflection i x) (reflection_reflection i x) (realization i x z)

theorem reflectedRealization_val (z : ForestOrthantRealization.Ambient i x) :
    (reflectedRealization i x z).val = realization i x z :=
  projection_eq (tree i x) (reflection i x) (reflection_reflection i x) _
    ⟨radiusArray_reflection i x z, (shapeArray_constraints i x z).2.1⟩

theorem contDiff_reflectedRealization : ContDiff ℝ ⊤ (reflectedRealization i x) :=
  (projection (tree i x) (reflection i x) (reflection_reflection i x)).contDiff.comp (contDiff_realization i x)

def Regular (z : ForestOrthantRealization.Ambient i x) : Prop :=
  ForestGraphForms.Regular (shapeData i x) (reflectedRealization i x z)

theorem isOpen_regular : IsOpen {z | Regular i x z} :=
  (ForestGraphForms.isOpen_regular (shapeData i x)).preimage (contDiff_reflectedRealization i x).continuous

theorem regular_source (z : ForestOrthantCharts.Model i x)
    (hz : z ∈ (ForestOrthantCharts.chart i x).source) : Regular i x (includeOrthant i x z) := by
  change ForestDirectionRatioCoordinates.RegularUnits (tree i x) (canonicalLeaf i x)
    (reflectedRealization i x (includeOrthant i x z)).val
  rw [reflectedRealization_val]
  exact (realization_admissible i x z hz).2

/-- The actual ordered graph form pulled back along the smooth realization
into the genuine reflected tangent subspace. -/
def graphForm {r : ℕ} (edges : Fin r → Edge n m) (z : ForestOrthantRealization.Ambient i x) :
    ForestOrthantRealization.Ambient i x [⋀^Fin r]→L[ℝ] ℝ :=
  (ForestGraphTopForms.topForm (shapeData i x) edges (reflectedRealization i x z)).compContinuousLinearMap
    (fderiv ℝ (reflectedRealization i x) z)

theorem eventually_graphForm_potential {r : ℕ} (edges : Fin r → Edge n m)
    (z : ForestOrthantRealization.Ambient i x) (hz : Regular i x z) :
    graphForm i x edges =ᶠ[𝓝 z] fun y => (coordinateVolume r).compContinuousLinearMap
      (fderiv ℝ (ForestGraphTopForms.potentialMap (shapeData i x) edges (reflectedRealization i x z) ∘
        reflectedRealization i x) y) := by
  have he := (ForestGraphTopForms.eventually_topForm_eq_potentialPullback (shapeData i x) edges
    (reflectedRealization i x z) hz).comp_tendsto (contDiff_reflectedRealization i x).continuous.continuousAt
  have hd := (ForestGraphTopForms.contDiffAt_potentialMap (shapeData i x) edges (reflectedRealization i x z) hz).eventually (by simp : (⊤ : ℕ∞ω) ≠ ∞)
  have hd' := ((contDiff_reflectedRealization i x).continuous.tendsto z).eventually hd
  filter_upwards [he, hd'] with y hy hdy
  simp only [Function.comp_def] at hy
  rw [graphForm, hy, fderiv_comp y (hdy.differentiableAt (by simp))
      ((contDiff_reflectedRealization i x).differentiable (by simp)).differentiableAt]
  rfl

theorem contDiffAt_graphForm {r : ℕ} (edges : Fin r → Edge n m)
    (z : ForestOrthantRealization.Ambient i x) (hz : Regular i x z) :
    ContDiffAt ℝ ⊤ (graphForm i x edges) z := by
  have hp := (ForestGraphTopForms.contDiffAt_potentialMap (shapeData i x) edges (reflectedRealization i x z) hz).comp z (contDiff_reflectedRealization i x).contDiffAt
  have hD : ContDiffAt ℝ ⊤ (fderiv ℝ
      (ForestGraphTopForms.potentialMap (shapeData i x) edges (reflectedRealization i x z) ∘
        reflectedRealization i x)) z := hp.fderiv_right (by simp)
  have h := (contDiff_compContinuousLinearMap (coordinateVolume r)).contDiffAt.comp z hD
  exact h.congr_of_eventuallyEq (eventually_graphForm_potential i x edges z hz)

theorem extDeriv_graphForm {r : ℕ} (edges : Fin r → Edge n m)
    (z : ForestOrthantRealization.Ambient i x) (hz : Regular i x z) :
    extDeriv (graphForm i x edges) z = 0 := by
  change extDeriv (fun y => (ForestGraphTopForms.topForm (shapeData i x) edges (reflectedRealization i x y)).compContinuousLinearMap (fderiv ℝ (reflectedRealization i x) y)) z = 0
  rw [extDeriv_pullback
    ((ForestGraphTopForms.contDiffAt_topForm (shapeData i x) edges (reflectedRealization i x z) hz).differentiableAt (by simp))
    (contDiff_reflectedRealization i x).contDiffAt (by simp),
    ForestGraphTopForms.extDeriv_topForm (shapeData i x) edges (reflectedRealization i x z) hz]
  ext v
  rfl

theorem contDiffAt_graphForm_source {r : ℕ} (edges : Fin r → Edge n m)
    (z : ForestOrthantCharts.Model i x) (hz : z ∈ (ForestOrthantCharts.chart i x).source) :
    ContDiffAt ℝ ⊤ (graphForm i x edges) (includeOrthant i x z) :=
  contDiffAt_graphForm i x edges _ (regular_source i x z hz)

theorem extDeriv_graphForm_source {r : ℕ} (edges : Fin r → Edge n m)
    (z : ForestOrthantCharts.Model i x) (hz : z ∈ (ForestOrthantCharts.chart i x).source) :
    extDeriv (graphForm i x edges) (includeOrthant i x z) = 0 :=
  extDeriv_graphForm i x edges _ (regular_source i x z hz)

def realizedEdge (e : Edge n m) : ForestOrthantRealization.Ambient i x → ℂ × ℂ :=
  ForestGraphForms.edgeMap (shapeData i x) e.source e.target ∘ reflectedRealization i x

theorem contDiff_realizedEdge (e : Edge n m) : ContDiff ℝ ⊤ (realizedEdge i x e) :=
  (ForestGraphForms.contDiff_edgeMap (shapeData i x) e.source e.target).comp (contDiff_reflectedRealization i x)

theorem realizedEdge_denominator_ne (e : Edge n m) (z : ForestOrthantRealization.Ambient i x)
    (hz : Regular i x z) (hpos : ForestMarkedFrameInverse.PositiveInternal (tree i x) (realization i x z).1) :
    (realizedEdge i x e z).2 - conj (realizedEdge i x e z).1 ≠ 0 := by
  have hp : ForestMarkedFrameInverse.PositiveInternal (tree i x) (reflectedRealization i x z).val.1 := by
    rw [reflectedRealization_val]
    exact hpos
  change (ForestGraphForms.edgeMap (shapeData i x) e.source e.target (reflectedRealization i x z)).2 -
    conj (ForestGraphForms.edgeMap (shapeData i x) e.source e.target (reflectedRealization i x z)).1 ≠ 0
  rw [congrFun (ForestGraphForms.denominator_factorization (shapeData i x) e.source e.target) (reflectedRealization i x z)]
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (ForestGraphForms.radialScale_pos (shapeData i x) _ _ hp).ne')
    (hz (harmonicDenominatorPair e.source e.target))

theorem graphForm_harmonicDeterminant {r : ℕ} (edges : Fin r → Edge n m)
    (z : ForestOrthantRealization.Ambient i x) (hz : Regular i x z)
    (hpos : ForestMarkedFrameInverse.PositiveInternal (tree i x) (realization i x z).1)
    (v : Fin r → ForestOrthantRealization.Ambient i x) : graphForm i x edges z v =
      Matrix.det (fun a b => ((harmonicAngleForm (realizedEdge i x (edges b) z)).compContinuousLinearMap
        (fderiv ℝ (realizedEdge i x (edges b)) z)) (fun _ : Fin 1 => v a)) := by
  have hp : ForestMarkedFrameInverse.PositiveInternal (tree i x) (reflectedRealization i x z).val.1 := by
    rw [reflectedRealization_val]
    exact hpos
  rw [graphForm, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    ForestGraphTopForms.topForm_eq_harmonicDeterminant (shapeData i x) edges _ hz hp]
  congr 1
  funext a b
  rw [realizedEdge, fderiv_comp z
    ((ForestGraphForms.contDiff_edgeMap (shapeData i x) (edges b).source (edges b).target).differentiable (by simp)).differentiableAt
    ((contDiff_reflectedRealization i x).differentiable (by simp)).differentiableAt]
  rfl

/-- Parameter-dependent positive anchor normalization retains every derivative
of its scale and real shift; its determinant of edge pullbacks is exactly the
actual extended forest graph form on the positive locus. -/
theorem graphForm_variableAffineDeterminant {r : ℕ} (edges : Fin r → Edge n m)
    (s b : ForestOrthantRealization.Ambient i x → ℝ) (z : ForestOrthantRealization.Ambient i x)
    (hs : DifferentiableAt ℝ s z) (hb : DifferentiableAt ℝ b z) (hspos : 0 < s z)
    (hz : Regular i x z) (hpos : ForestMarkedFrameInverse.PositiveInternal (tree i x) (realization i x z).1)
    (v : Fin r → ForestOrthantRealization.Ambient i x) : graphForm i x edges z v =
      Matrix.det (fun a k => ((harmonicAngleForm (variableAffinePair (realizedEdge i x (edges k)) s b z)).compContinuousLinearMap
        (fderiv ℝ (variableAffinePair (realizedEdge i x (edges k)) s b) z)) (fun _ : Fin 1 => v a)) := by
  rw [graphForm_harmonicDeterminant i x edges z hz hpos v]
  congr 1
  funext a k
  rw [harmonicAngleForm_variableAffine_pullback (realizedEdge i x (edges k)) s b z
    ((contDiff_realizedEdge i x (edges k)).differentiable (by simp)).differentiableAt hs hb hspos
    (realizedEdge_denominator_ne i x (edges k) z hz hpos)]

section NativeComparison

variable {k : ℕ} (i : Fin (k + 1)) (x : Compactification i m)

/-- Chain rule for the literal native GraphForms determinant, in its original
edge order, through a varying original-coordinate map. -/
theorem native_pullback_determinant {r : ℕ} (edges : Fin r → GraphForms.Edge k m)
    (f : ForestOrthantRealization.Ambient i x → GraphForms.Coordinates k m)
    (z : ForestOrthantRealization.Ambient i x) (hf : DifferentiableAt ℝ f z)
    (v : Fin r → ForestOrthantRealization.Ambient i x) :
    (GraphForms.topForm edges (f z)).compContinuousLinearMap (fderiv ℝ f z) v =
      Matrix.det (fun a b => ((harmonicAngleForm ((GraphForms.edgeMap (edges b) ∘ f) z)).compContinuousLinearMap
        (fderiv ℝ (GraphForms.edgeMap (edges b) ∘ f) z)) (fun _ : Fin 1 => v a)) := by
  rw [ContinuousAlternatingMap.compContinuousLinearMap_apply, GraphForms.topForm_apply]
  congr 1
  funext a b
  rw [GraphForms.edgeForm_eq_pullback,
    fderiv_comp z (GraphForms.hasFDerivAt_edgeMap (edges b) (f z)).differentiableAt hf]
  rfl

/-- Exact native graph-form comparison from the actual varying affine endpoint
identities. The hypotheses concern only the concrete point-coordinate maps;
no equality of forms or omission of normalization derivatives is assumed. -/
theorem graphForm_eq_native_of_edgeMaps {r : ℕ} (edges : Fin r → Edge (k + 1) m)
    (native : Fin r → GraphForms.Edge k m)
    (f : ForestOrthantRealization.Ambient i x → GraphForms.Coordinates k m)
    (s b : ForestOrthantRealization.Ambient i x → ℝ) (z : ForestOrthantRealization.Ambient i x)
    (hf : DifferentiableAt ℝ f z) (hs : DifferentiableAt ℝ s z) (hb : DifferentiableAt ℝ b z)
    (hspos : 0 < s z) (hz : Regular i x z)
    (hpos : ForestMarkedFrameInverse.PositiveInternal (tree i x) (realization i x z).1)
    (hmap : ∀ j, (GraphForms.edgeMap (native j) ∘ f) =ᶠ[𝓝 z]
      variableAffinePair (realizedEdge i x (edges j)) s b) :
    graphForm i x edges z = (GraphForms.topForm native (f z)).compContinuousLinearMap (fderiv ℝ f z) := by
  ext v
  rw [graphForm_variableAffineDeterminant i x edges s b z hs hb hspos hz hpos v,
    native_pullback_determinant i x native f z hf v]
  congr 1
  funext a j
  rw [(hmap j).self_of_nhds, (hmap j).fderiv_eq]

end NativeComparison

end EnvelopingIsomorphism.Deformation.Kontsevich.ForestOrthantGraphForms
