import EnvelopingIsomorphism.Deformation.Kontsevich.BoundedLogMonomialCombination

/-! Conversion of finitely many actual unit bounds into the common constants
used by the monomial determinant estimates. No form estimate is assumed. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.BoundedLogMonomialCombination

open Set MeasureTheory
open scoped BigOperators

variable {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype I]

/-- Finite individual unit estimates give a single strictly positive bound. -/
theorem exists_uniform_unit_bounds (u : I → E → ℂ) (s : Set E)
    (h : ∀ i, ∃ C : ℝ, 0 < C ∧ ∀ x ∈ s,
      ‖u i x‖ ≤ C ∧ ‖(u i x)⁻¹‖ ≤ C ∧ ‖fderiv ℝ (u i) x‖ ≤ C) :
    ∃ C : ℝ, 0 < C ∧ ∀ i x, x ∈ s →
      ‖u i x‖ ≤ C ∧ ‖(u i x)⁻¹‖ ≤ C ∧ ‖fderiv ℝ (u i) x‖ ≤ C := by
  classical
  choose C hC hb using h
  have hsum : 0 ≤ ∑ i, C i := Finset.sum_nonneg (fun i _ ↦ (hC i).le)
  refine ⟨1 + ∑ i, C i, by linarith, ?_⟩
  intro i x hx
  have hle : C i ≤ 1 + ∑ i, C i := by
    have hh := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) ↦ (hC j).le)
      (Finset.mem_univ i)
    linarith
  exact ⟨(hb i x hx).1.trans hle, (hb i x hx).2.1.trans hle,
    (hb i x hx).2.2.trans hle⟩

variable {J K : Type*} [Fintype J] [Fintype K] {n : ℕ}

/-- Build the analytic input from actual C2 units with bounds on their values,
reciprocals and real derivatives. All three numerical constants are derived. -/
def LocalData.ofUnitBounds
    (a : Fin (n + 1) → J → ℤ) (b : K → J → ℤ)
    (u : Fin (n + 1) → (J → ℂ) → ℂ) (q : K → (J → ℂ) → ℂ)
    (radius : J → ℝ) (region : Set (J → ℂ)) (hregion : MeasurableSet region)
    (hdisc : region ⊆ NormalCrossing.puncturedPolydisc radius)
    (U : Set (J → ℂ)) (hU : IsOpen U) (hregionU : region ⊆ U)
    (hu : ∀ j, ContDiffOn ℝ 2 (u j) U) (hq : ∀ k, ContDiffOn ℝ 2 (q k) U)
    (hu0 : ∀ j x, x ∈ region → u j x ≠ 0)
    (hq0 : ∀ k x, x ∈ region → q k x ≠ 0)
    (hub : ∀ j, ∃ C : ℝ, 0 < C ∧ ∀ x ∈ region,
      ‖u j x‖ ≤ C ∧ ‖(u j x)⁻¹‖ ≤ C ∧ ‖fderiv ℝ (u j) x‖ ≤ C)
    (hqb : ∀ k, ∃ C : ℝ, 0 < C ∧ ∀ x ∈ region,
      ‖q k x‖ ≤ C ∧ ‖(q k x)⁻¹‖ ≤ C ∧ ‖fderiv ℝ (q k) x‖ ≤ C) : LocalData J K n := by
  let units : Fin (n + 1) ⊕ K → (J → ℂ) → ℂ := Sum.elim u q
  have hb : ∀ i, ∃ C : ℝ, 0 < C ∧ ∀ x ∈ region,
      ‖units i x‖ ≤ C ∧ ‖(units i x)⁻¹‖ ≤ C ∧ ‖fderiv ℝ (units i) x‖ ≤ C := by
    intro i
    cases i with
    | inl j => exact hub j
    | inr k => exact hqb k
  let C := (exists_uniform_unit_bounds units region hb).choose
  have hC : 0 < C := (exists_uniform_unit_bounds units region hb).choose_spec.1
  have hbound := (exists_uniform_unit_bounds units region hb).choose_spec.2
  refine {
    a := a, b := b, u := u, q := q, radius := radius, region := region
    measurable_region := hregion, region_polydisc := hdisc
    U := U, open_U := hU, region_U := hregionU
    units_C2 := hu, extra_units_C2 := hq
    D := C, c := 1 / C, M := C, c_pos := one_div_pos.mpr hC
    unit_lower := ?_, extra_unit_lower := ?_
    unit_derivative := fun x hx j ↦ (hbound (Sum.inl j) x hx).2.2
    extra_unit_derivative := fun x hx k ↦ (hbound (Sum.inr k) x hx).2.2
    first_unit_upper := fun x hx ↦ (hbound (Sum.inl 0) x hx).1 }
  · intro x hx j
    apply (one_div_le hC (norm_pos_iff.mpr (hu0 j x hx))).mpr
    have hi : ‖(u j x)⁻¹‖ ≤ C := (hbound (Sum.inl j) x hx).2.1
    simpa only [one_div, norm_inv] using hi
  · intro x hx k
    apply (one_div_le hC (norm_pos_iff.mpr (hq0 k x hx))).mpr
    have hi : ‖(q k x)⁻¹‖ ≤ C := (hbound (Sum.inr k) x hx).2.1
    simpa only [one_div, norm_inv] using hi

end EnvelopingIsomorphism.Deformation.Kontsevich.BoundedLogMonomialCombination
