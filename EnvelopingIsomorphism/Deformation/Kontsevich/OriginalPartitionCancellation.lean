import EnvelopingIsomorphism.Deformation.Kontsevich.OriginalDRSmooth
import EnvelopingIsomorphism.Deformation.Kontsevich.FiniteForestPartition

/-! Actual original-chart smooth partition pieces and cancellation of their exterior derivatives. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.OriginalPartitionCancellation

open Set Filter ContinuousAlternatingMap
open scoped BigOperators Classical Topology Manifold ContDiff

section ExteriorCalculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {r : ℕ}
    {J : Type*} [Fintype J]

abbrev Form (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (r : ℕ) :=
  E → E [⋀^Fin r]→L[ℝ] ℝ

/-- Actual scalar localization of a differential form. -/
def localized (ρ : E → ℝ) (form : Form E r) : Form E r := fun x => ρ x • form x

/-- The genuine derivative-of-cutoff term, in the native exterior derivative convention. -/
def cutoffTerm (ρ : E → ℝ) (form : Form E r) (x : E) : E [⋀^Fin (r + 1)]→L[ℝ] ℝ :=
  alternatizeUncurryFin ((fderiv ℝ ρ x).smulRight (form x))

theorem extDeriv_localized (ρ : E → ℝ) (form : Form E r) (x : E)
    (hρ : DifferentiableAt ℝ ρ x) (hform : DifferentiableAt ℝ form x) :
    extDeriv (localized ρ form) x = ρ x • extDeriv form x + cutoffTerm ρ form x := by
  change extDeriv (fun y => ρ y • form y) x = _
  rw [extDeriv, fderiv_fun_smul hρ hform, alternatizeUncurryFin_add, alternatizeUncurryFin_smul]
  rfl

theorem extDeriv_finiteSum (η : J → Form E r) (x : E)
    (hη : ∀ j, DifferentiableAt ℝ (η j) x) :
    extDeriv (fun y => ∑ j, η j y) x = ∑ j, extDeriv (η j) x := by
  change (alternatizeUncurryFinCLM ℝ _ ℝ) (fderiv ℝ (fun y => ∑ j, η j y) x) = _
  rw [fderiv_fun_sum (fun j hj => hη j), _root_.map_sum]
  rfl

/-- Genuine finite derivative linearity and the local partition identity. -/
theorem sum_extDeriv_localized (ρ : J → E → ℝ) (form : Form E r) (x : E)
    (hρ : ∀ j, DifferentiableAt ℝ (ρ j) x) (hform : DifferentiableAt ℝ form x)
    (hsum : (fun y => ∑ j, ρ j y) =ᶠ[𝓝 x] fun _ => (1 : ℝ)) :
    (∑ j, extDeriv (localized (ρ j) form) x) = extDeriv form x := by
  have hdiff : ∀ j, DifferentiableAt ℝ (localized (ρ j) form) x := fun j => (hρ j).smul hform
  rw [← extDeriv_finiteSum (fun j => localized (ρ j) form) x hdiff]
  have he : (fun y => ∑ j, localized (ρ j) form y) =ᶠ[𝓝 x] form := by
    filter_upwards [hsum] with y hy
    simp only [localized, ← Finset.sum_smul, hy, one_smul]
  exact he.extDeriv_eq

/-- The individual dρ wedges cancel by the actual scalar partition product rule. -/
theorem sum_cutoffTerm_zero (ρ : J → E → ℝ) (form : Form E r) (x : E)
    (hρ : ∀ j, DifferentiableAt ℝ (ρ j) x) (hform : DifferentiableAt ℝ form x)
    (hsum : (fun y => ∑ j, ρ j y) =ᶠ[𝓝 x] fun _ => (1 : ℝ)) :
    (∑ j, cutoffTerm (ρ j) form x) = 0 := by
  have h := sum_extDeriv_localized ρ form x hρ hform hsum
  simp only [extDeriv_localized _ _ x (hρ _) hform, Finset.sum_add_distrib,
    ← Finset.sum_smul, hsum.self_of_nhds, one_smul] at h
  exact add_left_cancel (h.trans (add_zero _).symm)

end ExteriorCalculus

variable {n m : ℕ} {J : Type*} [Fintype J]

abbrev Ambient (n m : ℕ) := Fin (CompactDRCoordinates.dimension (n + 1) m) → ℝ

abbrev Partition (J : Type*) (n m : ℕ) :=
  SmoothPartitionOfUnity J 𝓘(ℝ, Ambient n m) (Ambient n m)
    (range (CompactDRCoordinates.embedding (m := m) (0 : Fin (n + 1))))

/-- The actual ambient scalar cutoff pulled into the original raw coordinates. -/
def pullCutoff (ρ : Ambient n m → ℝ) (x : GraphForms.Coordinates n m) : ℝ :=
  ρ (OriginalDRSmooth.real x)

theorem pullCutoff_eq_global (ρ : Ambient n m → ℝ) (x : GraphForms.CoordinateDomain n m) :
    pullCutoff ρ x.val = CompactDRAmbientPartition.cutoff 0 ρ (OriginalDRSmooth.originalPoint x) :=
  congrArg ρ (OriginalDRSmooth.real_eq_embedding x)

theorem contDiffAt_pullCutoff (ρ : Ambient n m → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    {x : GraphForms.Coordinates n m} (hx : GraphForms.Admissible x) :
    ContDiffAt ℝ ∞ (pullCutoff ρ) x :=
  hρ.contDiffAt.comp x ((OriginalDRSmooth.contDiffAt_real hx).of_le le_top)

theorem partition_sum (η : Partition J n m) {x : GraphForms.Coordinates n m} (hx : GraphForms.Admissible x) :
    (∑ j, pullCutoff (η j) x) = 1 := by
  have hpoint : OriginalDRSmooth.real x ∈ range
      (CompactDRCoordinates.embedding (m := m) (0 : Fin (n + 1))) :=
    ⟨OriginalDRSmooth.originalPoint ⟨x, hx⟩, (OriginalDRSmooth.real_eq_embedding ⟨x, hx⟩).symm⟩
  simpa only [finsum_eq_sum_of_fintype, pullCutoff] using η.sum_eq_one hpoint

theorem partition_sum_eventually (η : Partition J n m)
    {x : GraphForms.Coordinates n m} (hx : GraphForms.Admissible x) :
    (fun y => ∑ j, pullCutoff (η j) y) =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
  filter_upwards [(GraphForms.isOpen_admissibleSet n m).mem_nhds hx] with y hy
  exact partition_sum η hy

omit [Fintype J] in
theorem contDiffAt_partition_cutoff (η : Partition J n m) (j : J)
    {x : GraphForms.Coordinates n m} (hx : GraphForms.Admissible x) :
    ContDiffAt ℝ ∞ (pullCutoff (η j)) x :=
  contDiffAt_pullCutoff _ (CompactSmoothPartition.partition_contDiff η j) hx

omit [Fintype J] in
/-- Every actual partition-localized graph form is smooth on the original open domain. -/
theorem contDiffAt_graphPiece (η : Partition J n m) (j : J) {r : ℕ}
    (edges : Fin r → GraphForms.Edge n m)
    (he : ∀ a, (edges a).target ≠ Sum.inl (edges a).source)
    {x : GraphForms.Coordinates n m} (hx : GraphForms.Admissible x) :
    ContDiffAt ℝ ∞ (localized (pullCutoff (η j)) (GraphForms.topForm edges)) x :=
  (contDiffAt_partition_cutoff η j hx).smul ((GraphForms.contDiffAt_topForm edges he hx).of_le le_top)

/-- Finite derivative cancellation for the actual closed graph form, with no
Stokes or integral identity assumed. -/
theorem sum_extDeriv_graphPieces_zero (η : Partition J n m) {r : ℕ}
    (edges : Fin r → GraphForms.Edge n m)
    (he : ∀ a, (edges a).target ≠ Sum.inl (edges a).source)
    {x : GraphForms.Coordinates n m} (hx : GraphForms.Admissible x) :
    (∑ j, extDeriv (localized (pullCutoff (η j)) (GraphForms.topForm edges)) x) = 0 := by
  rw [sum_extDeriv_localized _ _ x
    (fun j => (contDiffAt_partition_cutoff η j hx).differentiableAt (by simp))
    ((GraphForms.contDiffAt_topForm edges he hx).differentiableAt (by simp))
    (partition_sum_eventually η hx)]
  exact GraphForms.extDeriv_topForm_eq_zero edges he hx

/-- In particular all actual cutoff derivative wedges cancel pointwise. -/
theorem sum_cutoffTerm_graphPieces_zero (η : Partition J n m) {r : ℕ}
    (edges : Fin r → GraphForms.Edge n m)
    (he : ∀ a, (edges a).target ≠ Sum.inl (edges a).source)
    {x : GraphForms.Coordinates n m} (hx : GraphForms.Admissible x) :
    (∑ j, cutoffTerm (pullCutoff (η j)) (GraphForms.topForm edges) x) = 0 :=
  sum_cutoffTerm_zero _ _ x
    (fun j => (contDiffAt_partition_cutoff η j hx).differentiableAt (by simp))
    ((GraphForms.contDiffAt_topForm edges he hx).differentiableAt (by simp))
    (partition_sum_eventually η hx)

/-- The already constructed genuine finite forest partition supplies actual smooth
original-chart pieces with partition and derivative cancellation, without a supplied
partition-existence or chart-transition hypothesis. -/
theorem exists_finite_original_partition {r : ℕ}
    (edges : Fin r → GraphForms.Edge n m)
    (he : ∀ a, (edges a).target ≠ Sum.inl (edges a).source) :
    ∃ (s : Finset (Compactification (0 : Fin (n + 1)) m)) (η : Partition s n m),
      (∀ y : Compactification (0 : Fin (n + 1)) m,
        ∃ j : s, y ∈ (ForestChartOpenImage.parameterChart 0 j.val).target) ∧
      (∀ j : s, HasCompactSupport (fun y => η j y)) ∧
      (∀ j : s, tsupport (CompactDRAmbientPartition.cutoff 0 (η j)) ⊆
        (ForestChartOpenImage.parameterChart 0 j.val).target) ∧
      (∀ j : s, ContDiffOn ℝ ∞ (pullCutoff (η j)) (GraphForms.admissibleSet n m)) ∧
      (∀ x : GraphForms.Coordinates n m, GraphForms.Admissible x → (∑ j, pullCutoff (η j) x) = 1) ∧
      ∀ x : GraphForms.Coordinates n m, GraphForms.Admissible x →
        (∑ j, extDeriv (localized (pullCutoff (η j)) (GraphForms.topForm edges)) x) = 0 := by
  obtain ⟨s, η, hcover, _, hcpt, hsub, _⟩ :=
    FiniteForestPartition.exists_finite_ambient_partition (m := m) (0 : Fin (n + 1))
  exact ⟨s, η, hcover, hcpt, hsub,
    fun j x hx => (contDiffAt_partition_cutoff η j hx).contDiffWithinAt,
    fun x hx => partition_sum η hx,
    fun x hx => sum_extDeriv_graphPieces_zero η edges he hx⟩

end EnvelopingIsomorphism.Deformation.Kontsevich.OriginalPartitionCancellation
