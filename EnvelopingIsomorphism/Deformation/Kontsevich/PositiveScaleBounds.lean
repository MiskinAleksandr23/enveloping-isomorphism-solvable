import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Fintype.Basic

/-! Uniform positive scales for finitely many displacement constraints,
and a quantitative noncollision criterion for linear complex motions. -/

namespace EnvelopingIsomorphism.Deformation.Kontsevich

/-- Finitely many nonnegative displacement magnitudes admit one positive
scale below all positive separation bounds. The index type may be empty. -/
theorem exists_uniform_pos_mul_lt {ι : Type*} [Finite ι]
    (a b : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 < b i) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i, ε * a i < b i := by
  classical
  letI := Fintype.ofFinite ι
  have hfinite : ∀ s : Finset ι, ∃ ε : ℝ, 0 < ε ∧ ∀ i ∈ s, ε * a i < b i := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨1, zero_lt_one, by simp⟩
    | @insert i s hi ih =>
      obtain ⟨ε, hε, hbound⟩ := ih
      obtain ⟨δ, hδ, hiδ⟩ := exists_pos_mul_lt (hb i) (a i)
      refine ⟨min ε δ, lt_min hε hδ, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with hji | hj
      · subst j
        exact (mul_le_mul_of_nonneg_right (min_le_right ε δ) (ha i)).trans_lt
          (by simpa only [mul_comm] using hiδ)
      · exact (mul_le_mul_of_nonneg_right (min_le_left ε δ) (ha j)).trans_lt (hbound j hj)
  obtain ⟨ε, hε, hbound⟩ := hfinite Finset.univ
  exact ⟨ε, hε, fun i => hbound i (Finset.mem_univ i)⟩

/-- If relative displacement is strictly smaller than the initial separation,
the two translated complex points cannot collide. -/
theorem add_real_mul_ne_of_mul_norm_lt (r : ℝ) (hr : 0 ≤ r) (p q v w : ℂ)
    (h : r * ‖v - w‖ < ‖p - q‖) : p + (r : ℂ) * v ≠ q + (r : ℂ) * w := by
  intro heq
  have hdiff : p - q = (r : ℂ) * (w - v) := by
    rw [mul_sub, sub_eq_sub_iff_add_eq_add]
    simpa only [add_comm] using heq
  have hnorm : ‖p - q‖ = r * ‖v - w‖ := by
    rw [hdiff, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr, norm_sub_rev w v]
  exact (ne_of_lt h) hnorm.symm

end EnvelopingIsomorphism.Deformation.Kontsevich
