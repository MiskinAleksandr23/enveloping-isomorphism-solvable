import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Compactly supported smooth partitions near a compact Euclidean set

The functions are provided by Mathlib's native `SmoothPartitionOfUnity`.
Their supports are bounded by first intersecting the cover with a large ball.
A closed thickening makes their sum equal to one on an open neighborhood of
the original compact set.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.CompactSmoothPartition

open Set Metric Function
open scoped Topology Manifold ContDiff

abbrev Space (d : ℕ) := Fin d → ℝ

/-- Native manifold smoothness becomes genuine Euclidean C-infinity smoothness.
Here `∞` is the smooth order; `⊤ : ℕ∞ω` would instead demand analyticity. -/
theorem partition_contDiff {d : ℕ} {ι : Type*} {K : Set (Space d)}
    (ρ : SmoothPartitionOfUnity ι 𝓘(ℝ, Space d) (Space d) K) (i : ι) :
    ContDiff ℝ ∞ (fun x => ρ i x) :=
  (ρ i).contMDiff.contDiff

theorem partition_contDiff_one {d : ℕ} {ι : Type*} {K : Set (Space d)}
    (ρ : SmoothPartitionOfUnity ι 𝓘(ℝ, Space d) (Space d) K) (i : ι) :
    ContDiff ℝ 1 (fun x => ρ i x) :=
  (partition_contDiff ρ i).of_le (by simp)

/-- Every finite open cover of a compact Euclidean set admits a native smooth
partition with compact supports subordinate to the same indexed cover. Its
sum is one on an open neighborhood contained in the union of the cover.
Both dimension zero and the empty-index/empty-compact case are allowed. -/
theorem exists_compact_smoothPartition {d : ℕ} {ι : Type*} [Fintype ι]
    (K : Set (Space d)) (hK : IsCompact K) (U : ι → Set (Space d))
    (hU : ∀ i, IsOpen (U i)) (hcover : K ⊆ ⋃ i, U i) :
    ∃ (O : Set (Space d)) (ρ : SmoothPartitionOfUnity ι 𝓘(ℝ, Space d) (Space d) K),
      IsOpen O ∧ K ⊆ O ∧ O ⊆ ⋃ i, U i ∧ ρ.IsSubordinate U ∧
      (∀ i, IsCompact (tsupport (ρ i))) ∧
      (∀ i, ContDiff ℝ ∞ (fun x => ρ i x)) ∧
      ∀ x ∈ O, ∑ i, ρ i x = 1 := by
  obtain ⟨R, hR, hKR⟩ := hK.isBounded.subset_ball_lt 0 (0 : Space d)
  let V : Set (Space d) := (⋃ i, U i) ∩ ball 0 R
  have hV : IsOpen V := (isOpen_iUnion hU).inter isOpen_ball
  have hKV : K ⊆ V := fun x hx => ⟨hcover hx, hKR hx⟩
  obtain ⟨δ, hδ, hδV⟩ := hK.exists_cthickening_subset_open hV hKV
  let L := cthickening δ K
  let W : ι → Set (Space d) := fun i => U i ∩ ball 0 R
  have hLW : L ⊆ ⋃ i, W i := by
    intro x hx
    obtain ⟨hxu, hxb⟩ := hδV hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hxu
    exact mem_iUnion.mpr ⟨i, hi, hxb⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, Space d)
    (s := L) isClosed_cthickening W (fun i => (hU i).inter isOpen_ball) hLW
  let ρK : SmoothPartitionOfUnity ι 𝓘(ℝ, Space d) (Space d) K :=
    { toFun := fun i => ρ i
      locallyFinite' := ρ.locallyFinite
      nonneg' := ρ.nonneg
      sum_eq_one' := fun x hx => ρ.sum_eq_one (self_subset_cthickening K hx)
      sum_le_one' := ρ.sum_le_one }
  refine ⟨thickening δ K, ρK, isOpen_thickening, self_subset_thickening hδ K, ?_, ?_, ?_,
    partition_contDiff ρK, ?_⟩
  · intro x hx
    exact (hδV (thickening_subset_cthickening δ K hx)).1
  · intro i x hx
    exact (hρ i hx).1
  · intro i
    apply (isCompact_closedBall (0 : Space d) R).of_isClosed_subset (isClosed_tsupport (ρK i))
    intro x hx
    exact ball_subset_closedBall (hρ i hx).2
  · intro x hx
    change ∑ i, ρ i x = 1
    simpa only [finsum_eq_sum_of_fintype] using
      ρ.sum_eq_one (thickening_subset_cthickening δ K hx)

end EnvelopingIsomorphism.Deformation.Kontsevich.CompactSmoothPartition
