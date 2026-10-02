import EnvelopingIsomorphism.Deformation.Kontsevich.CompactDRCoordinates

/-! Smooth full DR coordinates for a fixed collision mask. Mixed-scale ratios
are the actual constants zero and one; norms are taken only at nonzero units. -/
noncomputable section
namespace EnvelopingIsomorphism.Deformation.Kontsevich.StaticCollisionFaceDR
open Configuration
open scoped Classical
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n m : ℕ}
variable (C : DoubledPair n m → Prop) (B V : DoubledPair n m → E → ℂ)

def unit (p : DoubledPair n m) (y : E) : ℂ := if C p then V p y else B p y

def ratio (t : DoubledTriple n m) (y : E) : ℝ :=
  let p : DoubledPair n m := ⟨(t.val.1,t.val.2.1),t.property.1⟩
  let q : DoubledPair n m := ⟨(t.val.1,t.val.2.2),t.property.2⟩
  if C p ∧ ¬C q then 0 else if ¬C p ∧ C q then 1
  else ‖unit C B V p y‖ / (‖unit C B V p y‖ + ‖unit C B V q y‖)

def ambient (y : E) : CompactDRCoordinates.Ambient n m :=
  (fun p ↦ unit C B V p y / (‖unit C B V p y‖ : ℂ), fun t ↦ ratio C B V t y)

variable (y : E) (hz : ∀ p, B p y = 0 ↔ C p) (hv : ∀ p, C p → V p y ≠ 0)

include hz hv in
theorem unit_ne_zero (p : DoubledPair n m) : unit C B V p y ≠ 0 := by
  unfold unit
  split_ifs with h
  · exact hv p h
  · exact (hz p).not.mpr h

include hz hv in
theorem contDiffAt_ambient (hB : ∀ p, ContDiffAt ℝ ⊤ (B p) y)
    (hV : ∀ p, ContDiffAt ℝ ⊤ (V p) y) : ContDiffAt ℝ ⊤ (ambient C B V) y := by
  have hu (p) : ContDiffAt ℝ ⊤ (unit C B V p) y := by
    unfold unit
    split_ifs
    · exact hV p
    · exact hB p
  have hn (p) := unit_ne_zero C B V y hz hv p
  apply ContDiffAt.prodMk
  · apply contDiffAt_pi.mpr
    intro p
    have hr := Complex.ofRealCLM.contDiff.contDiffAt.comp y ((hu p).norm ℝ (hn p))
    simpa only [div_eq_mul_inv, Pi.inv_apply, Function.comp_apply, Complex.ofRealCLM_apply] using
      (hu p).mul (hr.inv (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (hn p))))
  · apply contDiffAt_pi.mpr
    intro t
    dsimp only [ratio]
    split_ifs
    · exact contDiffAt_const
    · exact contDiffAt_const
    · exact ((hu _).norm ℝ (hn _)).div (((hu _).norm ℝ (hn _)).add ((hu _).norm ℝ (hn _)))
        (add_pos (norm_pos_iff.mpr (hn _)) (norm_pos_iff.mpr (hn _))).ne'

include hz hv in
/-- Exact pointwise identity with the genuine linear-collision limits. -/
theorem ambient_eq_limits : ambient C B V y =
    (fun p ↦ (linearPhaseLimit (B p y) (V p y) : ℂ),
      fun t ↦ ((linearRatioLimit
        (B ⟨(t.val.1,t.val.2.1),t.property.1⟩ y) (B ⟨(t.val.1,t.val.2.2),t.property.2⟩ y)
        (V ⟨(t.val.1,t.val.2.1),t.property.1⟩ y) (V ⟨(t.val.1,t.val.2.2),t.property.2⟩ y)) : ℝ)) := by
  apply Prod.ext
  · funext p
    change unit C B V p y / (‖unit C B V p y‖ : ℂ) = _
    rw [← complexPhase_coe (unit_ne_zero C B V y hz hv p)]
    unfold unit linearPhaseLimit
    by_cases hp : C p
    · simp [hp, (hz p).mpr hp]
    · simp [hp, (hz p).not.mpr hp]
  · funext t
    let p : DoubledPair n m := ⟨(t.val.1,t.val.2.1),t.property.1⟩
    let q : DoubledPair n m := ⟨(t.val.1,t.val.2.2),t.property.2⟩
    change ratio C B V t y = (linearRatioLimit (B p y) (B q y) (V p y) (V q y) : ℝ)
    have hn (e) (he : ¬C e) : ‖B e y‖ ≠ 0 := norm_ne_zero_iff.mpr ((hz e).not.mpr he)
    by_cases hp : C p <;> by_cases hq : C q
    · simp only [ratio, show C ⟨(t.val.1,t.val.2.1),t.property.1⟩ from hp,
        show C ⟨(t.val.1,t.val.2.2),t.property.2⟩ from hq,
        not_true_eq_false, and_false, false_and, if_false, unit, if_pos,
        linearRatioLimit, (hz p).mpr hp, (hz q).mpr hq, and_self, normalizedNormRatio]
      rfl
    · simp [ratio, unit, linearRatioLimit, hp, hq, (hz p).mpr hp, (hz q).not.mpr hq,
        normalizedNormRatio, p, q] at *
    · simp [ratio, unit, linearRatioLimit, hp, hq, (hz q).mpr hq, (hz p).not.mpr hp,
        normalizedNormRatio, hn p hp, p, q] at *
    · simp [ratio, unit, linearRatioLimit, hp, hq, (hz p).not.mpr hp, (hz q).not.mpr hq,
        normalizedNormRatio, p, q] at *

end EnvelopingIsomorphism.Deformation.Kontsevich.StaticCollisionFaceDR
