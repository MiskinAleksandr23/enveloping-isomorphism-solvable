import EnvelopingIsomorphism.Deformation.Kontsevich.LocalChartDominatedConvergence
import EnvelopingIsomorphism.Deformation.Kontsevich.InteriorFiberAngleSplit
import Mathlib.Topology.MetricSpace.PartitionOfUnity
import Mathlib.MeasureTheory.MeasurableSpace.Embedding

/-! A native continuous partition on the collision-complement subtype, extended
by zero to ambient coordinates. A finite open chart cover suffices; the open
configuration space need not be compact. No derivative of a partition weight
is used in the local-to-global integral argument. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.FiniteChartPartition

open Set MeasureTheory Function
open scoped BigOperators Topology

variable {E J : Type*} [MetricSpace E] [Fintype J]

/-- Native partition on the whole subtype, which is closed in itself. -/
theorem exists_subordinate (Ω : Set E) (U : J → Set E)
    (hU : ∀ j, IsOpen (U j)) (hcover : Ω ⊆ ⋃ j, U j) :
    ∃ ρ : PartitionOfUnity J Ω, ρ.IsSubordinate (fun j ↦ Subtype.val ⁻¹' U j) := by
  apply PartitionOfUnity.exists_isSubordinate isClosed_univ
  · intro j
    exact (hU j).preimage continuous_subtype_val
  · intro x hx
    rcases mem_iUnion.mp (hcover x.property) with ⟨j, hj⟩
    exact mem_iUnion.mpr ⟨j, hj⟩

/-- A selected native continuous partition, built only from the actual cover. -/
def partition (Ω : Set E) (U : J → Set E)
    (hU : ∀ j, IsOpen (U j)) (hcover : Ω ⊆ ⋃ j, U j) : PartitionOfUnity J Ω :=
  (exists_subordinate Ω U hU hcover).choose

theorem partition_subordinate (Ω : Set E) (U : J → Set E)
    (hU : ∀ j, IsOpen (U j)) (hcover : Ω ⊆ ⋃ j, U j) :
    (partition Ω U hU hcover).IsSubordinate (fun j ↦ Subtype.val ⁻¹' U j) :=
  (exists_subordinate Ω U hU hcover).choose_spec

/-- Genuine zero extension along the subtype inclusion. It need not be
continuous across the collision set, and this construction does not claim so. -/
def extension (Ω : Set E) (ρ : PartitionOfUnity J Ω) (j : J) : E → ℝ :=
  Function.extend Subtype.val (ρ j) (fun _ ↦ 0)

@[simp] theorem extension_mem (Ω : Set E) (ρ : PartitionOfUnity J Ω) (j : J)
    {x : E} (hx : x ∈ Ω) : extension Ω ρ j x = ρ j ⟨x, hx⟩ :=
  Subtype.val_injective.extend_apply (ρ j) (fun _ ↦ 0) ⟨x, hx⟩

theorem extension_not_mem (Ω : Set E) (ρ : PartitionOfUnity J Ω) (j : J)
    {x : E} (hx : x ∉ Ω) : extension Ω ρ j x = 0 := by
  apply Function.extend_apply'
  rintro ⟨y, rfl⟩
  exact hx y.property

theorem extension_nonneg (Ω : Set E) (ρ : PartitionOfUnity J Ω) (j : J) (x : E) :
    0 ≤ extension Ω ρ j x := by
  by_cases hx : x ∈ Ω
  · rw [extension_mem Ω ρ j hx]
    exact ρ.nonneg j _
  · rw [extension_not_mem Ω ρ j hx]

theorem extension_le_one (Ω : Set E) (ρ : PartitionOfUnity J Ω) (j : J) (x : E) :
    extension Ω ρ j x ≤ 1 := by
  by_cases hx : x ∈ Ω
  · rw [extension_mem Ω ρ j hx]
    exact ρ.le_one j _
  · rw [extension_not_mem Ω ρ j hx]
    exact zero_le_one

theorem norm_extension_le_one (Ω : Set E) (ρ : PartitionOfUnity J Ω) (j : J) (x : E) :
    ‖extension Ω ρ j x‖ ≤ 1 := by
  rw [Real.norm_of_nonneg (extension_nonneg Ω ρ j x)]
  exact extension_le_one Ω ρ j x

theorem sum_extension (Ω : Set E) (ρ : PartitionOfUnity J Ω) {x : E} (hx : x ∈ Ω) :
    ∑ j, extension Ω ρ j x = 1 := by
  simp only [extension_mem Ω ρ _ hx]
  simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one (show (⟨x, hx⟩ : Ω) ∈ (univ : Set Ω) from mem_univ _)

/-- Subordination on the subtype gives actual ambient vanishing off each chart image. -/
theorem extension_zero_off_target (Ω : Set E) (ρ : PartitionOfUnity J Ω)
    (U : J → Set E) (hρ : ρ.IsSubordinate (fun j ↦ Subtype.val ⁻¹' U j))
    (j : J) {x : E} (hx : x ∉ U j) : extension Ω ρ j x = 0 := by
  by_cases hxΩ : x ∈ Ω
  · rw [extension_mem Ω ρ j hxΩ]
    by_contra hn
    exact hx (hρ j (subset_tsupport (ρ j) hn))
  · exact extension_not_mem Ω ρ j hxΩ

/-- The extension retains the native continuity on the original open domain. -/
theorem continuousOn_extension (Ω : Set E) (ρ : PartitionOfUnity J Ω) (j : J) :
    ContinuousOn (extension Ω ρ j) Ω := by
  rw [continuousOn_iff_continuous_restrict]
  have he : Ω.restrict (extension Ω ρ j) = ρ j := by
    funext x
    exact extension_mem Ω ρ j x.property
  rw [he]
  exact (ρ j).continuous

variable [MeasurableSpace E] [BorelSpace E]

/-- The subtype inclusion is a measurable embedding; its literal zero
extension is globally measurable even at the collision set. -/
theorem measurable_extension (Ω : Set E) (hΩ : MeasurableSet Ω)
    (ρ : PartitionOfUnity J Ω) (j : J) : Measurable (extension Ω ρ j) :=
  (MeasurableEmbedding.subtype_coe hΩ).measurable_extend (ρ j).continuous.measurable measurable_const

/-- All ambient partition properties, derived from the native partition. -/
theorem exists_partition_weights (Ω : Set E) (hΩ : MeasurableSet Ω) (U : J → Set E)
    (hU : ∀ j, IsOpen (U j)) (hcover : Ω ⊆ ⋃ j, U j) :
    ∃ ρ : PartitionOfUnity J Ω,
      ρ.IsSubordinate (fun j ↦ Subtype.val ⁻¹' U j) ∧
      (∀ j, Measurable (extension Ω ρ j)) ∧
      (∀ j x, 0 ≤ extension Ω ρ j x ∧ extension Ω ρ j x ≤ 1) ∧
      (∀ x ∈ Ω, ∑ j, extension Ω ρ j x = 1) ∧
      (∀ j x, x ∉ U j → extension Ω ρ j x = 0) := by
  let ρ := partition Ω U hU hcover
  have hρ := partition_subordinate Ω U hU hcover
  exact ⟨ρ, hρ, measurable_extension Ω hΩ ρ,
    fun j x ↦ ⟨extension_nonneg Ω ρ j x, extension_le_one Ω ρ j x⟩,
    fun x hx ↦ sum_extension Ω ρ hx, fun j x hx ↦ extension_zero_off_target Ω ρ U hρ j hx⟩

end FiniteChartPartition

namespace FiniteChartPartition

open Set MeasureTheory InteriorFiberAngleSplit
open scoped BigOperators Topology

variable {N : ℕ} {J : Type*} [Fintype J]

/-- Actual normalized collision-complement specialization. Compactness of the
configuration space is neither required nor asserted. -/
theorem exists_shape_partition_weights (U : J → Set (Shape N))
    (hU : ∀ j, IsOpen (U j)) (hcover : shapeConfiguration N ⊆ ⋃ j, U j) :
    ∃ ρ : PartitionOfUnity J (shapeConfiguration N),
      ρ.IsSubordinate (fun j ↦ Subtype.val ⁻¹' U j) ∧
      (∀ j, Measurable (extension (shapeConfiguration N) ρ j)) ∧
      (∀ j η, 0 ≤ extension (shapeConfiguration N) ρ j η ∧
        extension (shapeConfiguration N) ρ j η ≤ 1) ∧
      (∀ η ∈ shapeConfiguration N, ∑ j, extension (shapeConfiguration N) ρ j η = 1) ∧
      (∀ j η, η ∉ U j → extension (shapeConfiguration N) ρ j η = 0) :=
  exists_partition_weights (shapeConfiguration N) (isOpen_shapeConfiguration N).measurableSet U hU hcover

open BoxStokes LocalChartDominatedConvergence

/-- Complete the actual change-of-variables chart cover from its geometric
cover data. Every partition field is constructed, with no weight hypothesis. -/
def chartCover {d : ℕ} (Ω : Set (Coord d)) (hΩ : IsOpen Ω)
    (φ : J → Coord d → Coord d) (S : J → Set (Coord d))
    (hS : ∀ j, MeasurableSet (S j))
    (hφ : ∀ j, ∀ x ∈ S j, ContDiffAt ℝ 1 (φ j) x)
    (hinj : ∀ j, InjOn (φ j) (S j))
    (him : ∀ j, φ j '' S j ⊆ Ω) (hopen : ∀ j, IsOpen (φ j '' S j))
    (hcover : Ω ⊆ ⋃ j, φ j '' S j) : ChartCover d J where
  domain := Ω
  open_domain := hΩ
  chart := φ
  source := S
  measurable_source := hS
  chart_C1 := hφ
  chart_injective := hinj
  image_domain := him
  weight := extension Ω (partition Ω (fun j ↦ φ j '' S j) hopen hcover)
  weight_nonneg := fun _ _ j ↦ extension_nonneg Ω _ j _
  sum_weight := fun _ hx ↦ sum_extension Ω _ hx
  weight_zero := fun j _ _ hy ↦ extension_zero_off_target Ω _ _
    (partition_subordinate Ω (fun j ↦ φ j '' S j) hopen hcover) j hy

/-- The constructed real-coordinate chart weights are measurable, uniformly bounded,
and continuous on the original domain. -/
theorem chartCover_weight_properties {d : ℕ} (Ω : Set (Coord d)) (hΩ : IsOpen Ω)
    (φ : J → Coord d → Coord d) (S : J → Set (Coord d))
    (hS : ∀ j, MeasurableSet (S j))
    (hφ : ∀ j, ∀ x ∈ S j, ContDiffAt ℝ 1 (φ j) x)
    (hinj : ∀ j, InjOn (φ j) (S j))
    (him : ∀ j, φ j '' S j ⊆ Ω) (hopen : ∀ j, IsOpen (φ j '' S j))
    (hcover : Ω ⊆ ⋃ j, φ j '' S j) (j : J) :
    let c := chartCover Ω hΩ φ S hS hφ hinj him hopen hcover
    Measurable (c.weight j) ∧ ContinuousOn (c.weight j) Ω ∧ ∀ x, ‖c.weight j x‖ ≤ 1 := by
  exact ⟨measurable_extension Ω hΩ.measurableSet _ j,
    continuousOn_extension Ω _ j, norm_extension_le_one Ω _ j⟩

section RealCoordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] {d : ℕ}

/-- The literal chart map in a chosen real continuous-linear coordinate system. -/
def realChart (L : Coord d ≃L[ℝ] E) (φ : E → E) : Coord d → Coord d :=
  fun x ↦ L.symm (φ (L x))

theorem realChart_image (L : Coord d ≃L[ℝ] E) (φ : E → E) (S : Set E) :
    realChart L φ '' (L ⁻¹' S) = L ⁻¹' (φ '' S) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨L y, hy, by simp [realChart]⟩
  · rintro ⟨y, hy, hxy⟩
    refine ⟨L.symm y, by simpa using hy, ?_⟩
    simp only [realChart, L.apply_symm_apply, hxy, L.symm_apply_apply]

/-- Actual charts on a complex or other real normed space give the preceding
real-coordinate chart cover through any chosen continuous linear equivalence.
The partition and all its required weights are constructed after transport. -/
def chartCover_via_linearEquiv (L : Coord d ≃L[ℝ] E)
    (Ω : Set E) (hΩ : IsOpen Ω) (φ : J → E → E) (S : J → Set E)
    (hS : ∀ j, MeasurableSet (S j))
    (hφ : ∀ j, ∀ x ∈ S j, ContDiffAt ℝ 1 (φ j) x)
    (hinj : ∀ j, InjOn (φ j) (S j))
    (him : ∀ j, φ j '' S j ⊆ Ω) (hopen : ∀ j, IsOpen (φ j '' S j))
    (hcover : Ω ⊆ ⋃ j, φ j '' S j) : ChartCover d J := by
  apply chartCover (L ⁻¹' Ω) (hΩ.preimage L.continuous)
    (fun j ↦ realChart L (φ j)) (fun j ↦ L ⁻¹' S j)
  · exact fun j ↦ (hS j).preimage L.continuous.measurable
  · intro j x hx
    exact L.symm.contDiff.contDiffAt.comp x ((hφ j (L x) hx).comp x L.contDiff.contDiffAt)
  · intro j x hx y hy hxy
    exact L.injective (hinj j hx hy (L.symm.injective hxy))
  · intro j
    rw [realChart_image]
    exact preimage_mono (him j)
  · intro j
    rw [realChart_image]
    exact (hopen j).preimage L.continuous
  · intro x hx
    rcases mem_iUnion.mp (hcover hx) with ⟨j, hj⟩
    apply mem_iUnion.mpr
    refine ⟨j, ?_⟩
    rw [realChart_image]
    exact hj

/-- The real-coordinate adapter exposes the measurable bounded weights needed
by local dominated convergence directly. -/
theorem chartCover_via_linearEquiv_weight_properties (L : Coord d ≃L[ℝ] E)
    (Ω : Set E) (hΩ : IsOpen Ω) (φ : J → E → E) (S : J → Set E)
    (hS : ∀ j, MeasurableSet (S j))
    (hφ : ∀ j, ∀ x ∈ S j, ContDiffAt ℝ 1 (φ j) x)
    (hinj : ∀ j, InjOn (φ j) (S j))
    (him : ∀ j, φ j '' S j ⊆ Ω) (hopen : ∀ j, IsOpen (φ j '' S j))
    (hcover : Ω ⊆ ⋃ j, φ j '' S j) (j : J) :
    let c := chartCover_via_linearEquiv L Ω hΩ φ S hS hφ hinj him hopen hcover
    Measurable (c.weight j) ∧ ContinuousOn (c.weight j) (L ⁻¹' Ω) ∧
      ∀ x, ‖c.weight j x‖ ≤ 1 := by
  exact ⟨measurable_extension _ (hΩ.preimage L.continuous).measurableSet _ j,
    continuousOn_extension _ _ j, norm_extension_le_one _ _ j⟩

end RealCoordinates

end FiniteChartPartition

end EnvelopingIsomorphism.Deformation.Kontsevich
