import EnvelopingIsomorphism.Deformation.Kontsevich.ForestOrthantGraphForms
import EnvelopingIsomorphism.Deformation.Kontsevich.ChartCutoffSupport
import EnvelopingIsomorphism.Deformation.Kontsevich.CompactDRAmbientPartition

/-! Genuine compact smooth localization of orthant graph forms by the global
ambient partition and an actual constructed chart cutoff. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.ForestOrthantLocalization

open Configuration ForestOrthantRealization ForestOrthantGraphForms
open Set Filter Topology
open scoped Classical ContDiff NNReal

variable {n m : ℕ} (i : Fin n) (x : Compactification i m)

theorem continuous_includeOrthant : Continuous (includeOrthant i x) := by
  unfold includeOrthant
  fun_prop

def clamp (z : Ambient i x) : ForestOrthantCharts.Model i x :=
  (fun j => (z.1 j).toNNReal, z.2)

theorem continuous_clamp : Continuous (clamp i x) := by
  unfold clamp
  fun_prop

theorem clamp_include (z : ForestOrthantCharts.Model i x) : clamp i x (includeOrthant i x z) = z := by
  apply Prod.ext
  · funext j
    simp [clamp, includeOrthant]
  · rfl

theorem isEmbedding_includeOrthant : IsEmbedding (includeOrthant i x) :=
  Function.LeftInverse.isEmbedding (show Function.LeftInverse (clamp i x) (includeOrthant i x) from clamp_include i x)
    (continuous_clamp i x) (continuous_includeOrthant i x)

def Good : Set (Ambient i x) :=
  {z | ForestOrthantGraphForms.Regular i x z ∧ ContDiffAt ℝ ⊤ (ambientDR i x) z}

theorem isOpen_good : IsOpen (Good i x) := by
  apply isOpen_iff_mem_nhds.mpr
  intro z hz
  exact Filter.inter_mem ((ForestOrthantGraphForms.isOpen_regular i x).mem_nhds hz.1)
    (hz.2.eventually (by simp))

theorem source_good (z : ForestOrthantCharts.Model i x)
    (hz : z ∈ (ForestOrthantCharts.chart i x).source) : includeOrthant i x z ∈ Good i x :=
  ⟨regular_source i x z hz, contDiffAt_ambientDR i x z hz⟩

def realCoordinates : Ambient i x ≃L[ℝ] (Fin (Module.finrank ℝ (Ambient i x)) → ℝ) :=
  (Module.finBasis ℝ (Ambient i x)).equivFunL

theorem exists_smooth_cutoff (C U : Set (Ambient i x)) (hC : IsCompact C) (hU : IsOpen U) (hCU : C ⊆ U) :
    ∃ κ : Ambient i x → ℝ, ContDiff ℝ ∞ κ ∧ HasCompactSupport κ ∧ tsupport κ ⊆ U ∧
      EqOn κ (fun _ => 1) C := by
  let e := realCoordinates i x
  obtain ⟨κ, hsm, hcpt, hsub, hone⟩ := ChartCutoffSupport.exists_smooth_cutoff
    (e '' C) (e '' U) (hC.image e.continuous) (e.toHomeomorph.isOpenMap U hU) (Set.image_mono hCU)
  refine ⟨κ ∘ e, hsm.comp e.contDiff, hcpt.comp_homeomorph e.toHomeomorph, ?_, ?_⟩
  · intro z hz
    have hz' := tsupport_comp_subset_preimage κ e.continuous hz
    obtain ⟨w, hw, he⟩ := hsub hz'
    exact e.injective he ▸ hw
  · intro z hz
    exact hone (Set.mem_image_of_mem e hz)

variable (ρ : (Fin (CompactDRCoordinates.dimension n m) → ℝ) → ℝ)

abbrev globalCutoff := CompactDRAmbientPartition.cutoff i ρ

theorem exists_chart_cutoff
    (hsub : tsupport (globalCutoff i ρ) ⊆ (ForestOrthantCharts.chart i x).target) :
    ∃ (U : Set (Ambient i x)) (κ : Ambient i x → ℝ),
      IsOpen U ∧ (includeOrthant i x) ⁻¹' U = (ForestOrthantCharts.chart i x).source ∧
      U ⊆ Good i x ∧ ContDiff ℝ ∞ κ ∧ HasCompactSupport κ ∧ tsupport κ ⊆ U ∧
      EqOn κ (fun _ => 1) ((includeOrthant i x) '' ChartCutoffSupport.pulledSupport
        (ForestOrthantCharts.chart i x) (globalCutoff i ρ)) := by
  obtain ⟨V, hV, hpre⟩ := (isEmbedding_includeOrthant i x).isInducing.isOpen_iff.mp
    (ForestOrthantCharts.chart i x).open_source
  let U := V ∩ Good i x
  have hU : IsOpen U := hV.inter (isOpen_good i x)
  have hUpre : (includeOrthant i x) ⁻¹' U = (ForestOrthantCharts.chart i x).source := by
    ext z
    constructor
    · intro hz
      exact hpre ▸ hz.1
    · intro hz
      refine ⟨?_, source_good i x z hz⟩
      change z ∈ (includeOrthant i x) ⁻¹' V
      rw [hpre]
      exact hz
  let C := (includeOrthant i x) '' ChartCutoffSupport.pulledSupport
    (ForestOrthantCharts.chart i x) (globalCutoff i ρ)
  have hC : IsCompact C := (ChartCutoffSupport.isCompact_pulledSupport _ _ hsub).image (continuous_includeOrthant i x)
  have hCU : C ⊆ U := by
    rintro _ ⟨z, hz, rfl⟩
    have hs := ChartCutoffSupport.pulledSupport_subset_source _ _ hsub hz
    change z ∈ (includeOrthant i x) ⁻¹' U
    rw [hUpre]
    exact hs
  obtain ⟨κ, hsm, hcpt, hsupp, hone⟩ := exists_smooth_cutoff i x C U hC hU hCU
  exact ⟨U, κ, hU, hUpre, Set.inter_subset_right, hsm, hcpt, hsupp, hone⟩

def localized {r : ℕ} (edges : Fin r → ForestGraphTopForms.Edge n m) (κ : Ambient i x → ℝ) (z : Ambient i x) :
    Ambient i x [⋀^Fin r]→L[ℝ] ℝ := κ z • (ρ (ambientDR i x z) • graphForm i x edges z)

theorem contDiff_localized {r : ℕ} (edges : Fin r → ForestGraphTopForms.Edge n m)
    (hρ : ContDiff ℝ ∞ ρ) (κ : Ambient i x → ℝ) (hκ : ContDiff ℝ ∞ κ)
    (hgood : tsupport κ ⊆ Good i x) : ContDiff ℝ ∞ (localized i x ρ edges κ) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  by_cases hz : z ∈ tsupport κ
  · exact hκ.contDiffAt.smul
      ((hρ.contDiffAt.comp z ((hgood hz).2.of_le le_top)).smul
        ((contDiffAt_graphForm i x edges z (hgood hz).1).of_le le_top))
  · apply (contDiffAt_const (c := (0 : Ambient i x [⋀^Fin r]→L[ℝ] ℝ))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hz] with y hy
    simp [localized, hy]

theorem hasCompactSupport_localized {r : ℕ} (edges : Fin r → ForestGraphTopForms.Edge n m)
    (κ : Ambient i x → ℝ) (hκ : HasCompactSupport κ) : HasCompactSupport (localized i x ρ edges κ) :=
  hκ.smul_right

theorem localized_eq_orthant_piece {r : ℕ} (edges : Fin r → ForestGraphTopForms.Edge n m)
    (_hsub : tsupport (globalCutoff i ρ) ⊆ (ForestOrthantCharts.chart i x).target)
    (U : Set (Ambient i x)) (κ : Ambient i x → ℝ)
    (hpre : (includeOrthant i x) ⁻¹' U = (ForestOrthantCharts.chart i x).source)
    (hsupp : tsupport κ ⊆ U)
    (hone : EqOn κ (fun _ => 1) ((includeOrthant i x) '' ChartCutoffSupport.pulledSupport
      (ForestOrthantCharts.chart i x) (globalCutoff i ρ))) (z : ForestOrthantCharts.Model i x) :
    localized i x ρ edges κ (includeOrthant i x z) =
      ChartCutoffSupport.zeroPullback (ForestOrthantCharts.chart i x) (globalCutoff i ρ) z •
        graphForm i x edges (includeOrthant i x z) := by
  by_cases hz : z ∈ (ForestOrthantCharts.chart i x).source
  · rw [localized, ChartCutoffSupport.zeroPullback_source _ _ hz, ambientDR_eq_chart i x z hz]
    by_cases hzero : globalCutoff i ρ (ForestOrthantCharts.chart i x z) = 0
    · simp only [globalCutoff, CompactDRAmbientPartition.cutoff] at hzero
      simp [globalCutoff, CompactDRAmbientPartition.cutoff, hzero]
    · have hp : z ∈ ChartCutoffSupport.pulledSupport (ForestOrthantCharts.chart i x) (globalCutoff i ρ) :=
        ⟨ForestOrthantCharts.chart i x z, subset_tsupport _ hzero, (ForestOrthantCharts.chart i x).left_inv hz⟩
      rw [hone (Set.mem_image_of_mem _ hp), one_smul]
      rfl
  · have hκzero : κ (includeOrthant i x z) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro h
      exact hz (hpre ▸ hsupp h)
    simp [localized, hκzero, ChartCutoffSupport.zeroPullback_off_source _ _ hz]

/-- The cutoff and the genuinely compactly supported smooth ambient graph
form are constructed together, with exact agreement on the entire orthant. -/
theorem exists_localized_graphForm {r : ℕ} (edges : Fin r → ForestGraphTopForms.Edge n m)
    (hρ : ContDiff ℝ ∞ ρ)
    (hsub : tsupport (globalCutoff i ρ) ⊆ (ForestOrthantCharts.chart i x).target) :
    ∃ κ : Ambient i x → ℝ, ContDiff ℝ ∞ κ ∧ HasCompactSupport κ ∧
      ContDiff ℝ ∞ (localized i x ρ edges κ) ∧ HasCompactSupport (localized i x ρ edges κ) ∧
      ∀ z : ForestOrthantCharts.Model i x, localized i x ρ edges κ (includeOrthant i x z) =
        ChartCutoffSupport.zeroPullback (ForestOrthantCharts.chart i x) (globalCutoff i ρ) z •
          graphForm i x edges (includeOrthant i x z) := by
  obtain ⟨U, κ, hU, hpre, hgood, hsm, hcpt, hsupp, hone⟩ := exists_chart_cutoff i x ρ hsub
  exact ⟨κ, hsm, hcpt, contDiff_localized i x ρ edges hρ κ hsm (hsupp.trans hgood),
    hasCompactSupport_localized i x ρ edges κ hcpt,
    localized_eq_orthant_piece i x ρ edges hsub U κ hpre hsupp hone⟩

end EnvelopingIsomorphism.Deformation.Kontsevich.ForestOrthantLocalization
