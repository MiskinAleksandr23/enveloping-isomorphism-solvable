import EnvelopingIsomorphism.Deformation.Kontsevich.CompactDRAmbientPartition
import EnvelopingIsomorphism.Deformation.Kontsevich.ForestOrthantCharts

/-! A genuine finite angle/orthant forest-chart cover and a global ambient smooth partition.
No finite-atlas or partition hypothesis is supplied by the caller. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.FiniteForestOrthantPartition

open Set CompactDRCoordinates CompactDRAmbientPartition
open scoped Topology Manifold ContDiff Classical

variable {n m : ℕ} (i : Fin n)

theorem exists_finite_chart_cover :
    ∃ s : Finset (Compactification i m), ∀ y : Compactification i m,
      ∃ x : s, y ∈ (ForestOrthantCharts.chart i x.val).target := by
  let U : Compactification i m → Set (Compactification i m) :=
    fun x => (ForestOrthantCharts.chart i x).target
  have hcover : (univ : Set (Compactification i m)) ⊆ ⋃ x, U x := by
    intro y _
    exact mem_iUnion.mpr ⟨y, ForestOrthantCharts.mem_chart_target i y⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U
    (fun x => (ForestOrthantCharts.chart i x).open_target) hcover
  refine ⟨s, ?_⟩
  intro y
  have hy := hs (mem_univ y)
  simp only [mem_iUnion] at hy
  obtain ⟨x, hx, hy⟩ := hy
  exact ⟨⟨x, hx⟩, hy⟩

/-- Actual compactness and actual chart coverage produce finitely many ambient
smooth cutoffs, each supported in its chosen forest-chart target. -/
theorem exists_finite_ambient_partition :
    ∃ (s : Finset (Compactification i m))
      (ρ : SmoothPartitionOfUnity s 𝓘(ℝ, Euclidean (n := n) (m := m))
        (Euclidean (n := n) (m := m)) (range (embedding (m := m) i))),
      (∀ y : Compactification i m,
        ∃ x : s, y ∈ (ForestOrthantCharts.chart i x.val).target) ∧
      (∀ x : s, ContDiff ℝ ∞ (fun z => ρ x z)) ∧
      (∀ x : s, IsCompact (tsupport (ρ x))) ∧
      (∀ x : s, tsupport (cutoff i (ρ x)) ⊆
        (ForestOrthantCharts.chart i x.val).target) ∧
      ∀ y : Compactification i m, ∑ x : s, cutoff i (ρ x) y = 1 := by
  obtain ⟨s, hs⟩ := exists_finite_chart_cover (m := m) i
  obtain ⟨ρ, hsm, hcpt, hsub, hsum⟩ := exists_ambientPartition i
    (fun x : s => (ForestOrthantCharts.chart i x.val).target)
    (fun x => (ForestOrthantCharts.chart i x.val).open_target) hs
  exact ⟨s, ρ, hs, hsm, hcpt, hsub, hsum⟩

end EnvelopingIsomorphism.Deformation.Kontsevich.FiniteForestOrthantPartition
