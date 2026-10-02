import EnvelopingIsomorphism.Deformation.Kontsevich.CompactificationSequences
import EnvelopingIsomorphism.Deformation.Kontsevich.SubsetLimitPartitions

/-! Actual all-subset normalized limits above each point of the compactification.
The common subsequence still converges to the original compactification point,
so all its stored positions, doubled directions, and triple ratios are retained.
This is the analytic input to the finite hierarchy construction, with its full
existence proved from density and compactness. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.CompactificationClusterLimits

open Configuration Filter Topology SubsetNormalizedLimits
open scoped Classical

variable {n m : ℕ}

def doubledSequence (i : Fin n) (x : Compactification i m) (k : ℕ) : DoubledLabel n m → ℂ :=
  (normalizedSequence i x k).val.doubledPoint

theorem doubledSequence_injective (i : Fin n) (x : Compactification i m) (k : ℕ) :
    Function.Injective (doubledSequence i x k) :=
  (normalizedSequence i x k).val.doubledPoint_injective

/-- Every actual compactification point supplies all normalized cluster shapes
and all immediate child-scale limits on one genuine approximating subsequence. -/
theorem exists_all_subset_limits (i : Fin n) (x : Compactification i m) :
    ∃ (φ : ℕ → ℕ) (q : ShapeFamily (DoubledLabel n m)), StrictMono φ ∧
      Tendsto (fun k => compactificationEmbedding i (normalizedSequence i x (φ k))) atTop (𝓝 x) ∧
      (∀ A : LargeSubset (DoubledLabel n m),
        Tendsto (fun k => normalizedOn A (doubledSequence i x (φ k))) atTop (𝓝 (q A)) ∧
        q A (anchor A) = 0 ∧ ‖q A‖ = 1 ∧ ∃ j k, q A j ≠ q A k) ∧
      (∀ A : Finset (DoubledLabel n m), 1 < A.card →
        ∀ B ∈ (partition q A).parts, B.card < A.card) ∧
      (∀ A B : LargeSubset (DoubledLabel n m), B.val ∈ (partition q A.val).parts →
        Tendsto (fun k => radiusOn B (doubledSequence i x (φ k)) /
          radiusOn A (doubledSequence i x (φ k))) atTop (𝓝 0)) := by
  obtain ⟨φ, q, hφ, hq⟩ := exists_common_normalized_limits (doubledSequence i x) (doubledSequence_injective i x)
  refine ⟨φ, q, hφ, (tendsto_normalizedSequence i x).comp hφ.tendsto_atTop, hq, ?_, ?_⟩
  · exact partition_proper q (fun A => (hq A).2.2.2)
  · intro A B hB
    exact partition_child_ratio_tendsto_zero (doubledSequence i x) φ q (fun A => (hq A).1) A B hB

/-- A common extracted subsequence preserves every full doubled pair direction. -/
theorem tendsto_direction_subsequence (i : Fin n) (x : Compactification i m)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (p : DoubledPair n m) :
    Tendsto (fun k => complexPhase ((normalizedSequence i x (φ k)).val.pairDifference p)) atTop
      (𝓝 (x.val.2.1 p)) :=
  (tendsto_normalizedSequence_direction i x p).comp hφ.tendsto_atTop

/-- It also preserves every normalized triple-distance ratio, not only angles. -/
theorem tendsto_ratio_subsequence (i : Fin n) (x : Compactification i m)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (t : DoubledTriple n m) :
    Tendsto (fun k => (normalizedSequence i x (φ k)).val.tripleDistanceRatio t) atTop
      (𝓝 (x.val.2.2 t)) :=
  (tendsto_normalizedSequence_ratio i x t).comp hφ.tendsto_atTop

end EnvelopingIsomorphism.Deformation.Kontsevich.CompactificationClusterLimits
