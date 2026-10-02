import EnvelopingIsomorphism.Deformation.Kontsevich.ForestRadialFaceClassification

/-! Actual graph face integrals are supported on the chart source, and the
native measure can be restricted to its strict codimension-one part. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Kontsevich.ForestRadialFaceLocalization

open Set MeasureTheory BoxStokes CompactOrthantStokes OrthantInteriorIntegration
open ForestOrthantRealization ForestGlobalGraphStokes ForestRadialFaceClassification
open scoped Classical

variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r + 1)
  (x : Compactification (0 : Fin (n + 1)) m)
  (o : ForestRadialFaceClassification.Orbit 0 x)

def source : Set (Coord r) :=
  strictOrthant (faceIndices (radialIndices hdim x) (axis hdim x o)) ∩
    (fun z => ForestPositiveChartSmooth.ofAmbient 0 x (faceAmbient hdim x o z)) ⁻¹'
      (ForestOrthantCharts.chart 0 x).source

theorem continuous_faceAmbient : Continuous (faceAmbient hdim x o) :=
  (sourceCoordinates hdim x).symm.continuous.comp
    (by unfold faceEmbedding; fun_prop)

theorem isOpen_strictFace :
    IsOpen (strictOrthant (faceIndices (radialIndices hdim x) (axis hdim x o))) := by
  change IsOpen {z : Coord r | ∀ j ∈ faceIndices (radialIndices hdim x) (axis hdim x o), 0 < z j}
  simp only [setOf_forall]
  apply isOpen_iInter_of_finite
  intro j
  apply isOpen_iInter_of_finite
  intro _
  exact isOpen_lt continuous_const (continuous_apply j)

theorem measurableSet_source : MeasurableSet (source hdim x o) := by
  apply IsOpen.measurableSet
  unfold source
  apply (isOpen_strictFace hdim x o).inter
  exact (ForestOrthantCharts.chart 0 x).open_source.preimage
    ((ForestPositiveChartSmooth.continuous_ofAmbient 0 x).comp (continuous_faceAmbient hdim x o))

theorem faceAmbient_nonneg (z : Coord r)
    (hz : z ∈ strictOrthant (faceIndices (radialIndices hdim x) (axis hdim x o)))
    (j : Fin (ForestOrthantCharts.R 0 x)) : 0 ≤ (faceAmbient hdim x o z).1 j := by
  obtain ⟨o', rfl⟩ := (orbitEquiv 0 x).surjective j
  by_cases h : o' = o
  · subst o'
    rw [faceAmbient_selected_zero]
  · exact (faceAmbient_other_positive hdim x o o' z hz h).le

variable (ρ : OriginalPartitionCancellation.Ambient n m → ℝ)
  (edges : Fin r → GraphForms.Edge n m)
  (hloop : ∀ j, (edges j).target ≠ Sum.inl (edges j).source)
  (κ : Ambient 0 x → ℝ)

/-- This is the exact localization identity already constructed by global
forest Stokes, with the same local form and native graph edges. -/
def LocalizationAgreement : Prop :=
  ∀ w : ForestOrthantCharts.Model 0 x,
    ForestOrthantLocalization.localized 0 x ρ
      (fun a => ForestPositiveGraphForms.forestEdge 0 (edges a) (hloop a)) κ (includeOrthant 0 x w) =
      ChartCutoffSupport.zeroPullback (ForestOrthantCharts.chart 0 x)
        (CompactDRAmbientPartition.cutoff 0 ρ) w •
          ForestOrthantGraphForms.graphForm 0 x
            (fun a => ForestPositiveGraphForms.forestEdge 0 (edges a) (hloop a)) (includeOrthant 0 x w)

/-- No boundary change-of-variables assumption occurs: off-source vanishing
is obtained from the literal zero extension certificate. -/
theorem density_zero_off_source
    (hmatch : LocalizationAgreement x ρ edges hloop κ)
    (z : Coord r)
    (hz : z ∈ strictOrthant (faceIndices (radialIndices hdim x) (axis hdim x o)))
    (hnot : z ∉ source hdim x o) :
    facePullback (localForm hdim x ρ edges hloop κ) (axis hdim x o) 0 z (standardBasis r) = 0 := by
  have hchart : ForestPositiveChartSmooth.ofAmbient 0 x (faceAmbient hdim x o z) ∉
      (ForestOrthantCharts.chart 0 x).source := fun h => hnot ⟨hz, h⟩
  have hincl := ForestPositiveChartSmooth.includeOrthant_ofAmbient 0 x
    (faceAmbient hdim x o z) (faceAmbient_nonneg hdim x o z hz)
  have hzero := hmatch (ForestPositiveChartSmooth.ofAmbient 0 x (faceAmbient hdim x o z))
  rw [hincl, ChartCutoffSupport.zeroPullback_off_source _ _ hchart, zero_smul] at hzero
  simp only [facePullback, localForm, linearForm,
    ContinuousAlternatingMap.compContinuousLinearMap_apply]
  change ForestOrthantLocalization.localized 0 x ρ
    (fun a => ForestPositiveGraphForms.forestEdge 0 (edges a) (hloop a)) κ
      (faceAmbient hdim x o z) _ = 0
  rw [hzero]
  rfl

/-- The actual signed face integral is unchanged on restriction to the open
strict source where all forest-to-simple coordinate maps are defined. -/
theorem contribution_eq_integral_source
    (hmatch : LocalizationAgreement x ρ edges hloop κ) :
    contribution hdim x (localForm hdim x ρ edges hloop κ) o =
      -((-1 : ℝ) ^ (axis hdim x o).val) •
        ∫ z in source hdim x o,
          facePullback (localForm hdim x ρ edges hloop κ) (axis hdim x o) 0 z (standardBasis r) := by
  rw [contribution_eq_strict]
  congr 1
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    (isOpen_strictFace hdim x o).measurableSet
    (inter_subset_left : source hdim x o ⊆ _)
  intro z hz
  exact density_zero_off_source hdim x o ρ edges hloop κ hmatch z hz.1 hz.2

/-- The literal native face integrals with a specified geometric label class. -/
def classifiedContribution (k : Kind) : ℝ :=
  ∑ o : ForestRadialFaceClassification.Orbit 0 x, if kind 0 x o = k then
    -((-1 : ℝ) ^ (axis hdim x o).val) •
      ∫ z in source hdim x o,
        facePullback (localForm hdim x ρ edges hloop κ) (axis hdim x o) 0 z (standardBasis r)
    else 0

theorem lowerFaces_eq_sum_classified
    (hmatch : LocalizationAgreement x ρ edges hloop κ) :
    OrientedOrthantAssembly.lowerFaces (localForm hdim x ρ edges hloop κ) (radialIndices hdim x) =
      ∑ k : Kind, classifiedContribution hdim x ρ edges hloop κ k := by
  rw [lowerFaces_eq_sum_kinds]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro o _
  by_cases h : kind 0 x o = k
  · simp only [if_pos h]
    exact contribution_eq_integral_source hdim x o ρ edges hloop κ hmatch
  · simp only [if_neg h]

/-- Unconditional classified graph Stokes, retaining the actual finite
partition, source support, form regularity, and derived Jacobian orientation.
No measure, Stokes, boundary-matching, or localization hypothesis is supplied. -/
theorem exists_classified_boundary_cancellation
    (edges : Fin r → GraphForms.Edge n m)
    (hloop : ∀ j, (edges j).target ≠ Sum.inl (edges j).source) :
    ∃ (s : Finset (Compactification (0 : Fin (n + 1)) m))
      (ρ : OriginalPartitionCancellation.Partition s n m)
      (κ : ∀ j : s, Ambient 0 j.val → ℝ) (ε : s → ℝ),
      (∀ y : Compactification (0 : Fin (n + 1)) m,
        ∃ j : s, y ∈ (ForestChartOrientation.smallChart 0 j.val).target) ∧
      (∀ j : s, tsupport (CompactDRAmbientPartition.cutoff 0 (ρ j)) ⊆
        (ForestChartOrientation.smallChart 0 j.val).target) ∧
      (∀ j : s, ContDiff ℝ 1 (localForm hdim j.val (ρ j) edges hloop (κ j)) ∧
        HasCompactSupport (localForm hdim j.val (ρ j) edges hloop (κ j))) ∧
      (∀ j : s, LocalizationAgreement j.val (ρ j) edges hloop (κ j)) ∧
      (∀ j : s, ε j = 1 ∨ ε j = -1) ∧
      (∀ j : s, ∀ z ∈ positiveRegion hdim j.val,
        ε j * OrientedFormChangeVariables.jacobian (chart hdim j.val) z =
          |OrientedFormChangeVariables.jacobian (chart hdim j.val) z|) ∧
      ∑ j : s, ε j * ∑ k : Kind,
        classifiedContribution hdim j.val (ρ j) edges hloop (κ j) k = 0 := by
  obtain ⟨s, ρ, κ, ε, hcover, hsub, _, hθ, hmatch, hε, hjac, _, hsum⟩ :=
    ForestGlobalGraphStokes.exists_boundary_cancellation hdim edges hloop
  refine ⟨s, ρ, κ, ε, hcover, hsub, hθ, hmatch, hε, hjac, ?_⟩
  convert hsum using 1
  apply Finset.sum_congr rfl
  intro j _
  rw [lowerFaces_eq_sum_classified hdim j.val (ρ j) edges hloop (κ j) (hmatch j)]

end EnvelopingIsomorphism.Deformation.Kontsevich.ForestRadialFaceLocalization
