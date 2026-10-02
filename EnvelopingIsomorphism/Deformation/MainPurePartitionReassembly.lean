import EnvelopingIsomorphism.Deformation.MainPureFixedChartIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Finite reassembly of the original ambient partition on a physical pure
boundary face. The original cutoffs are evaluated in actual DR coordinates. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.MainPurePartitionReassembly
open Kontsevich Configuration ForestRadialFaceClassification
open PureForestSimpleCluster (lower upper)
open PureForestFaceChangeVariables MainPureFixedChartIntegral
open MeasureTheory
open scoped Classical BigOperators
variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r+1)
    (x : Compactification (0 : Fin (n+1)) m) (o : Orbit 0 x)
    (a b : Fin m) (ho : kind 0 x o = .pureBoundary)
    (hl : a.val = (lower x o).val) (hu : b.val + 1 = (upper x o).val) (hab : a < b)
    (hcard : (boundaryClusterBlock (lower x o) (upper x o)).card = 2)
    {J : Type*} [Fintype J] (ρ : OriginalPartitionCancellation.Partition J n m)

theorem sum_simpleCutoff (y : BoxStokes.Coord r)
    (hy : y ∈ simpleRegion hdim x o a b ho hl hu hab hcard) :
    (∑ j, simpleCutoff hdim x o a b ho hl hu hab hcard (ρ j) y) = 1 := by
  obtain ⟨D,hd⟩ := hy
  change (PureBoundaryClusterForms.dataCoarse D, PureBoundaryClusterForms.dataShape D) =
    (simpleCoordinates hdim x o a b ho hl hu hab hcard).symm y at hd
  simp_rw [simpleCutoff, ← hd, PureBoundaryFaceDR.ambient_data]
  simpa only [finsum_eq_sum_of_fintype, CompactDRCoordinates.embedding, compactProjectDR] using
    ρ.sum_eq_one (Set.mem_range_self D.boundaryPoint)

theorem simpleCutoff_nonneg (j : J) (y : BoxStokes.Coord r) :
    0 ≤ simpleCutoff hdim x o a b ho hl hu hab hcard (ρ j) y :=
  ρ.nonneg j _

theorem simpleCutoff_le_one (j : J) (y : BoxStokes.Coord r) :
    simpleCutoff hdim x o a b ho hl hu hab hcard (ρ j) y ≤ 1 :=
  ρ.le_one j _

private theorem measurable_ambient :
    Measurable (PureBoundaryFaceDR.ambient (n := n) (lower x o) (upper x o) a b) := by
  have hunit (p : DoubledPair (n+1) m) : Continuous
      (StaticCollisionFaceDR.unit (pureBoundaryClusterPairCollapses (lower x o) (upper x o))
        (PureBoundaryFaceDR.pairBase (lower x o) (upper x o) a b)
        (PureBoundaryFaceDR.pairVelocity (lower x o) (upper x o) a b) p) := by
    unfold StaticCollisionFaceDR.unit
    split_ifs
    · exact ((PureBoundaryFaceDR.contDiff_velocity _ _ a b p.val.2).sub
        (PureBoundaryFaceDR.contDiff_velocity _ _ a b p.val.1)).continuous
    · exact ((PureBoundaryFaceDR.contDiff_base _ _ a b p.val.2).sub
        (PureBoundaryFaceDR.contDiff_base _ _ a b p.val.1)).continuous
  unfold PureBoundaryFaceDR.ambient StaticCollisionFaceDR.ambient
  apply Measurable.prodMk
  · apply measurable_pi_lambda
    intro p
    exact (hunit p).measurable.div
      (Complex.continuous_ofReal.measurable.comp (hunit p).norm.measurable)
  · apply measurable_pi_lambda
    intro t
    unfold StaticCollisionFaceDR.ratio
    dsimp only
    split_ifs
    · exact measurable_const
    · exact measurable_const
    · exact (hunit _).norm.measurable.div ((hunit _).norm.measurable.add (hunit _).norm.measurable)

theorem measurable_simpleCutoff (j : J) :
    Measurable (simpleCutoff hdim x o a b ho hl hu hab hcard (ρ j)) :=
  (ρ j).property.continuous.measurable.comp
    ((CompactDRCoordinates.realCoordinates (n+1) m).continuous.measurable.comp
      ((measurable_ambient x o a b).comp
        (simpleCoordinates hdim x o a b ho hl hu hab hcard).symm.continuous.measurable))

theorem integrableOn_weight_mul (f : BoxStokes.Coord r → ℝ)
    (hf : IntegrableOn f (simpleRegion hdim x o a b ho hl hu hab hcard)) (j : J) :
    IntegrableOn (fun y ↦ simpleCutoff hdim x o a b ho hl hu hab hcard (ρ j) y * f y)
      (simpleRegion hdim x o a b ho hl hu hab hcard) :=
  hf.bdd_mul (measurable_simpleCutoff hdim x o a b ho hl hu hab hcard ρ j).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (simpleCutoff_nonneg hdim x o a b ho hl hu hab hcard ρ j y)]
      exact simpleCutoff_le_one hdim x o a b ho hl hu hab hcard ρ j y)

theorem sum_integral_weight_mul (f : BoxStokes.Coord r → ℝ)
    (hf : IntegrableOn f (simpleRegion hdim x o a b ho hl hu hab hcard)) :
    (∑ j, ∫ y in simpleRegion hdim x o a b ho hl hu hab hcard,
      simpleCutoff hdim x o a b ho hl hu hab hcard (ρ j) y * f y) =
      ∫ y in simpleRegion hdim x o a b ho hl hu hab hcard, f y := by
  rw [← integral_finsetSum _ (fun j _ ↦ integrableOn_weight_mul hdim x o a b ho hl hu hab hcard ρ f hf j)]
  apply setIntegral_congr_fun (measurableSet_simpleRegion hdim x o a b ho hl hu hab hcard)
  intro y hy
  dsimp only
  rw [← Finset.sum_mul, sum_simpleCutoff hdim x o a b ho hl hu hab hcard ρ y hy, one_mul]

end EnvelopingIsomorphism.Deformation.MainPurePartitionReassembly
