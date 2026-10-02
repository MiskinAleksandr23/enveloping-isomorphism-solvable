import EnvelopingIsomorphism.Deformation.Kontsevich.ForestChartOrientation

/-! Compactness supplies an actual finite cover by the smaller oriented forest
charts, and the ambient DR embedding supplies genuine smooth cutoffs. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.FiniteOrientedForestPartition

open Set ForestChartOrientation CompactDRAmbientPartition
open ForestGraphIntegrability OrientedFormChangeVariables MeasureTheory
open scoped Topology Manifold ContDiff Classical

variable {n m : ℕ} (i : Fin (n + 1))

theorem exists_finite_chart_cover :
    ∃ s : Finset (Compactification i m), ∀ y : Compactification i m,
      ∃ x : s, y ∈ (smallChart i x.val).target := by
  let U : Compactification i m → Set (Compactification i m) := fun x => (smallChart i x).target
  have hcover : (univ : Set (Compactification i m)) ⊆ ⋃ x, U x :=
    fun y _ => mem_iUnion.mpr ⟨y, mem_smallChart_target i y⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U (fun x => (smallChart i x).open_target) hcover
  refine ⟨s, fun y => ?_⟩
  have hy := hs (mem_univ y)
  simp only [mem_iUnion] at hy
  obtain ⟨x, hx, hy⟩ := hy
  exact ⟨⟨x, hx⟩, hy⟩

/-- All chart signs and all cutoffs are constructed, with no finite-atlas,
orientation, or partition hypothesis. -/
theorem exists_finite_oriented_partition :
    ∃ (s : Finset (Compactification i m))
      (ρ : SmoothPartitionOfUnity s 𝓘(ℝ, Euclidean (n := n + 1) (m := m))
        (Euclidean (n := n + 1) (m := m)) (range (CompactDRCoordinates.embedding (m := m) i)))
      (ε : s → ℝ),
      (∀ y : Compactification i m, ∃ x : s, y ∈ (smallChart i x.val).target) ∧
      (∀ x : s, ContDiff ℝ ∞ (fun z => ρ x z)) ∧
      (∀ x : s, IsCompact (tsupport (ρ x))) ∧
      (∀ x : s, tsupport (cutoff i (ρ x)) ⊆ (smallChart i x.val).target) ∧
      (∀ y : Compactification i m, ∑ x : s, cutoff i (ρ x) y = 1) ∧
      (∀ x : s, ε x = 1 ∨ ε x = -1) ∧
      (∀ x : s, ∀ z ∈ realPositiveBall i x.val,
        ε x * jacobian (coordinateChart i x.val) z = |jacobian (coordinateChart i x.val) z|) ∧
      ∀ x : s, ∀ η : TopForm (GraphForms.dimension n m),
        ε x * (∫ z in realPositiveBall i x.val,
          density (pullback (coordinateChart i x.val) η) z) =
            ∫ y in coordinateChart i x.val '' realPositiveBall i x.val, density η y := by
  obtain ⟨s, hs⟩ := exists_finite_chart_cover (m := m) i
  obtain ⟨ρ, hsm, hcpt, hsub, hsum⟩ := exists_ambientPartition i
    (fun x : s => (smallChart i x.val).target) (fun x => (smallChart i x.val).open_target) hs
  choose ε hε hsign hint using fun x : s => exists_orientation i x.val
  exact ⟨s, ρ, ε, hs, hsm, hcpt, hsub, hsum, hε, hsign, hint⟩

end EnvelopingIsomorphism.Deformation.Kontsevich.FiniteOrientedForestPartition
