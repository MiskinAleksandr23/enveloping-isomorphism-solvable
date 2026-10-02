import EnvelopingIsomorphism.Deformation.Kontsevich.ComplexForestFreeShapes

/-! Exact conversion of the actual normalized real forest arrays to the independent
Cartesian complex chart. Only nonzero phases, never a nonroot radius, are cancelled. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Kontsevich.ComplexForestPhaseCoordinates

open ComplexForestFreeShapes ComplexForestNormalizedCharts ComplexForestInsertion
open ForestChildShapeDecomposition ForestInsertionDifference InteriorFiberAngleSplit
open scoped Classical

variable (t : RootedTree) [Fintype t] (M : Marks t)

def phaseCoordinates (ρ : t → ℝ) (u a : t → ℂ) : Coordinates t M :=
  (fun v : Normal t ↦ complexWeight t ρ u v.val,
   fun p : Free t M ↦ a p.2.val.val / u p.1.val)

/-- These are precisely the zero-anchor and phase-reference equations in a
native normalized complex child frame. -/
def NativeMarks (u a : t → ℂ) : Prop :=
  ∀ v : Parent t, a (M.anchor v).val = 0 ∧ a (M.reference v).val = u v.val

theorem childShape_phaseCoordinates (ρ : t → ℝ) (u a : t → ℂ) (hu : ∀ v, u v ≠ 0)
    (ha : NativeMarks t M u a) (v : Parent t) (c : Child t v.val) :
    childShape t M (phaseCoordinates t M ρ u a).2 v c = a c.val / u v.val := by
  unfold childShape
  split_ifs with hc hc
  · subst c
    simp [(ha v).1]
  · subst c
    rw [(ha v).2, div_self (hu v.val)]
  · rfl

theorem shapeArray_phaseCoordinates_nonroot (ρ : t → ℝ) (u a : t → ℂ)
    (hu : ∀ v, u v ≠ 0) (ha : NativeMarks t M u a) (v : t) (hv : v ≠ ⊥) :
    shapeArray t M (phaseCoordinates t M ρ u a).2 v = normalizedIncrement t u a v := by
  let p := predecessorParent t v hv
  let c := predecessorChild t v hv
  have hh := shapeArray_child t M (phaseCoordinates t M ρ u a).2 p c
  change shapeArray t M (phaseCoordinates t M ρ u a).2 v = _ at hh
  rw [hh, childShape_phaseCoordinates t M ρ u a hu ha]
  exact (normalizedIncrement_child t u a c.property).symm

theorem phaseCartesian_eq (ρ : t → ℝ) (u a : t → ℂ)
    (hu : ∀ v, u v ≠ 0) (ha : NativeMarks t M u a) (v : t) :
    complexCartesian t (ComplexForestNormalizedCharts.includeParameters t
      (parameters t M (phaseCoordinates t M ρ u a))) v =
    complexCartesian t (ComplexForestNormalizedCharts.includeParameters t
      (fun k : Normal t ↦ complexWeight t ρ u k.val, normalizedIncrement t u a)) v := by
  apply complexCartesian_eq_of_internal_weights
  · intro k hk; rfl
  · intro k hk
    exact shapeArray_phaseCoordinates_nonroot t M ρ u a hu ha k hk

/-- The actual independent complex chart reconstructs the original real insertion,
up to its discarded common root scale and rotation, also at zero internal radii. -/
theorem position_phaseCoordinates (ρ : t → ℝ) (u a : t → ℂ)
    (hu : ∀ v, u v ≠ 0) (ha : NativeMarks t M u a) (v : t) :
    position t ρ a v = ((ρ ⊥ : ℂ) * u ⊥) *
      complexCartesian t (ComplexForestNormalizedCharts.includeParameters t
        (parameters t M (phaseCoordinates t M ρ u a))) v := by
  rw [phaseCartesian_eq t M ρ u a hu ha]
  exact phase_positions_root_factor t ρ u a hu v

/-- Exact old/new ratio compatibility, with no assumptions on the nonroot radii. -/
theorem pairRatio_phaseCoordinates (ρ : t → ℝ) (u a : t → ℂ)
    (hu : ∀ v, u v ≠ 0) (ha : NativeMarks t M u a) (hρ : ρ ⊥ ≠ 0) (v w b c : t) :
    (position t ρ a w - position t ρ a v) / (position t ρ a c - position t ρ a b) =
      ComplexForestInsertion.pairRatio t v w b c (ComplexForestNormalizedCharts.includeParameters t
        (parameters t M (phaseCoordinates t M ρ u a))) := by
  rw [phase_pairRatio t ρ u a hu hρ]
  simp only [ComplexForestInsertion.pairRatio, pairDifference,
    phaseCartesian_eq t M ρ u a hu ha]

def nativePhase (a : t → ℂ) (v : t) : ℂ :=
  if hv : IsMax v then 1 else a (M.reference ⟨v, hv⟩).val

def NormalizedShapes (a : t → ℂ) : Prop :=
  ∀ v : Parent t, a (M.anchor v).val = 0 ∧ ‖a (M.reference v).val‖ = 1

omit [Fintype t] in
theorem norm_nativePhase (a : t → ℂ) (ha : NormalizedShapes t M a) (v : t) :
    ‖nativePhase t M a v‖ = 1 := by
  unfold nativePhase
  split_ifs with hv
  · simp
  · exact (ha ⟨v, hv⟩).2

omit [Fintype t] in
theorem nativePhase_ne_zero (a : t → ℂ) (ha : NormalizedShapes t M a) (v : t) :
    nativePhase t M a v ≠ 0 := by
  intro h
  have hn := norm_nativePhase t M a ha v
  rw [h, norm_zero] at hn
  exact zero_ne_one hn

omit [Fintype t] in
theorem nativeMarks_nativePhase (a : t → ℂ) (ha : NormalizedShapes t M a) :
    NativeMarks t M (nativePhase t M a) a := by
  intro v
  exact ⟨(ha v).1, by simp [nativePhase, v.property]⟩

variable {N : ℕ} (lab : Point N → t)

theorem phaseCoordinates_mem_chartDomain (ρ : t → ℝ) (u a : t → ℂ)
    (hu : ∀ v, u v ≠ 0) (ha : NativeMarks t M u a)
    (hρ : ∀ v : Normal t, ρ v.val ≠ 0)
    (hpos : Function.Injective (fun j ↦ position t ρ a (lab j))) :
    phaseCoordinates t M ρ u a ∈ ComplexForestFreeShapes.chartDomain t M lab := by
  constructor
  · intro j k hjk hunit
    have hd : pairDifference t (ComplexForestNormalizedCharts.includeParameters t
        (parameters t M (phaseCoordinates t M ρ u a))) (lab j) (lab k) = 0 := by
      rw [pairDifference_factor, hunit, mul_zero]
    have he : position t ρ a (lab k) - position t ρ a (lab j) = 0 := by
      rw [position_phaseCoordinates t M ρ u a hu ha (lab k),
        position_phaseCoordinates t M ρ u a hu ha (lab j), ← mul_sub]
      exact mul_eq_zero_of_right _ hd
    exact (hpos.ne hjk) (sub_eq_zero.mp he).symm
  · intro v
    change complexWeight t ρ u v.val ≠ 0
    rw [complexWeight_nonroot t ρ u ((mem_normalNodes t v.val).mp v.property).1]
    exact div_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr (hρ v)) (hu v.val)) (hu _)

theorem normalized_pairRatio_phaseCoordinates (hinj : Function.Injective lab)
    (ρ : t → ℝ) (u a : t → ℂ) (hu : ∀ v, u v ≠ 0) (ha : NativeMarks t M u a)
    (hρ : ρ ⊥ ≠ 0)
    (hx : phaseCoordinates t M ρ u a ∈ ComplexForestFreeShapes.chartDomain t M lab)
    (j k b c : Point N) :
    (position t ρ a (lab k) - position t ρ a (lab j)) /
        (position t ρ a (lab c) - position t ρ a (lab b)) =
      shapeDifference j k (ComplexForestFreeShapes.chart t M lab (phaseCoordinates t M ρ u a)) /
        shapeDifference b c (ComplexForestFreeShapes.chart t M lab (phaseCoordinates t M ρ u a)) := by
  rw [pairRatio_phaseCoordinates t M ρ u a hu ha hρ]
  exact (ComplexForestNormalizedCharts.normalized_pairRatio t lab hinj hx j k b c).symm

end EnvelopingIsomorphism.Deformation.Kontsevich.ComplexForestPhaseCoordinates
