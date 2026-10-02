import EnvelopingIsomorphism.Deformation.Kontsevich.CompactDRCoordinates
import EnvelopingIsomorphism.Deformation.Kontsevich.CompactSmoothPartition
import EnvelopingIsomorphism.Deformation.Kontsevich.ForestChartConfigurations

/-! Genuine ambient smooth partitions subordinate to compactification charts.
Their pullbacks are smooth in every forest chart, independently of any
unproved smooth transition between different corner models. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.CompactDRAmbientPartition

open Set CompactDRCoordinates
open scoped Topology Manifold ContDiff

variable {n m : ℕ} (i : Fin n)
abbrev Euclidean := Fin (dimension n m) → ℝ

def cutoff (f : Euclidean (n := n) (m := m) → ℝ) (x : Compactification i m) : ℝ :=
  f (embedding i x)

/-- An actual finite open cover of the compactification admits cutoffs from
one fixed finite-dimensional real ambient space. -/
theorem exists_ambientPartition {ι : Type*} [Fintype ι]
    (U : ι → Set (Compactification i m)) (hU : ∀ j, IsOpen (U j))
    (hcover : ∀ x, ∃ j, x ∈ U j) :
    ∃ ρ : SmoothPartitionOfUnity ι 𝓘(ℝ, Euclidean (n := n) (m := m))
        (Euclidean (n := n) (m := m)) (range (embedding (m := m) i)),
      (∀ j, ContDiff ℝ ∞ (fun y => ρ j y)) ∧
      (∀ j, IsCompact (tsupport (ρ j))) ∧
      (∀ j, tsupport (cutoff i (ρ j)) ⊆ U j) ∧
      ∀ x, ∑ j, cutoff i (ρ j) x = 1 := by
  classical
  have hind := (isClosedEmbedding_embedding (m := m) i).isEmbedding.isInducing
  choose V hV hpre using fun j => hind.isOpen_iff.mp (hU j)
  have hcoverV : range (embedding (m := m) i) ⊆ ⋃ j, V j := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨j, hj⟩ := hcover x
    refine mem_iUnion.mpr ⟨j, ?_⟩
    change x ∈ embedding i ⁻¹' V j
    rw [hpre j]
    exact hj
  obtain ⟨O, ρ, hO, hKO, hOV, hsub, hcpt, hsm, hsum⟩ :=
    CompactSmoothPartition.exists_compact_smoothPartition _ (isCompact_range_embedding i) V hV hcoverV
  refine ⟨ρ, hsm, hcpt, ?_, ?_⟩
  · intro j x hx
    have ht : embedding i x ∈ tsupport (ρ j) :=
      tsupport_comp_subset_preimage (ρ j) (continuous_embedding i) hx
    have hm : x ∈ embedding i ⁻¹' V j := hsub j ht
    rwa [hpre j] at hm
  · intro x
    exact hsum (embedding i x) (hKO (mem_range_self x))

variable (T : RootedTree) [Fintype T]
variable (leaf : Configuration.DoubledLabel n m → T)

/-- Actual smoothness of every ambient cutoff in the already-proved forest
coordinate formula, including points with zero internal radii. -/
theorem contDiffAt_cutoff_forest (f : Euclidean (n := n) (m := m) → ℝ)
    (hf : ContDiff ℝ ∞ f) (x : ForestDirectionRatioCoordinates.Parameters T)
    (hx : ForestDirectionRatioCoordinates.Admissible T leaf x) :
    ContDiffAt ℝ ∞ (fun y => f (forestReal T leaf y)) x :=
  hf.contDiffAt.comp x ((contDiffAt_forestReal T leaf x hx).of_le le_top)

theorem embedding_forestInsertion (D : ForestPositiveScale.ShapeData T n m)
    (x : ForestChartConfigurations.CornerDomain D) :
    embedding i (ForestChartConfigurations.compactificationInsertion D i x) =
      forestReal T D.leaf x.val := by
  unfold embedding compactProjectDR
  rw [ForestChartConfigurations.compactificationInsertion_projectDR]
  rfl

theorem cutoff_forestInsertion (D : ForestPositiveScale.ShapeData T n m)
    (f : Euclidean (n := n) (m := m) → ℝ)
    (x : ForestChartConfigurations.CornerDomain D) :
    cutoff i f (ForestChartConfigurations.compactificationInsertion D i x) =
      f (forestReal T D.leaf x.val) := by
  rw [cutoff, embedding_forestInsertion]

end EnvelopingIsomorphism.Deformation.Kontsevich.CompactDRAmbientPartition
