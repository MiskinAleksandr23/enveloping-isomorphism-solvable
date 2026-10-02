import EnvelopingIsomorphism.Deformation.Kontsevich.RadialPoleDeterminant

/-! Uniform bounds for the actual finite coefficient sum of the radial-pole
determinant expansion. All bounds follow from entrywise data and finite counts.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.RadialPoleDeterminant

open scoped BigOperators

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- The permutation expansion gives a uniform determinant bound from its entry bounds. -/
theorem abs_det_le_card_perm (D : Matrix I I ℝ) (B₀ : ℝ)
    (hD : ∀ i j, |D i j| ≤ B₀) :
    |Matrix.det D| ≤ (Fintype.card (Equiv.Perm I) : ℝ) * B₀ ^ Fintype.card I := by
  classical
  rw [Matrix.det_apply]
  calc
    _ ≤ ∑ σ : Equiv.Perm I, |Equiv.Perm.sign σ • ∏ i, D (σ i) i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ σ : Equiv.Perm I, ∏ i, |D (σ i) i| := by
      apply Finset.sum_congr rfl
      intro σ hσ
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;>
        simp [hs, Finset.abs_prod]
    _ ≤ ∑ _σ : Equiv.Perm I, B₀ ^ Fintype.card I := by
      apply Finset.sum_le_sum
      intro σ hσ
      simpa only [Finset.prod_const, Finset.card_univ] using
        (Finset.prod_le_prod (s := Finset.univ) (fun i _ ↦ abs_nonneg (D (σ i) i))
          (fun i _ ↦ hD (σ i) i))
    _ = _ := by simp

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
theorem abs_selected_row_le (B : Matrix I I ℝ) (ρ : J → I → ℝ) (B₀ : ℝ)
    (hB : ∀ i j, |B i j| ≤ B₀) (hρ : ∀ ν j, |ρ ν j| ≤ B₀)
    (ε : I → Option J) (i j : I) : |row B ρ i (ε i) j| ≤ B₀ := by
  cases ε i with
  | none => exact hB i j
  | some ν => exact hρ ν j

omit [DecidableEq I] [Fintype J] [DecidableEq J] in
theorem abs_coefficient_product_le (c : I → J → ℝ) (C₀ : ℝ) (hC₀ : 1 ≤ C₀)
    (hc : ∀ i ν, |c i ν| ≤ C₀) (ε : I → Option J) :
    |∏ i, (ε i).elim 1 (c i)| ≤ C₀ ^ Fintype.card I := by
  classical
  rw [Finset.abs_prod]
  have hprod : (∏ i, |(ε i).elim 1 (c i)|) ≤ ∏ _i : I, C₀ := by
    apply Finset.prod_le_prod (fun i _ ↦ abs_nonneg ((ε i).elim 1 (c i)))
    intro i hi
    cases ε i with
    | none => simpa using hC₀
    | some ν => exact hc i ν
  simpa only [Finset.prod_const, Finset.card_univ] using hprod

omit [Fintype J] [DecidableEq J] in
/-- Each original smooth coefficient is bounded, whether or not its radial labels are distinct. -/
theorem abs_smoothCoefficient_le (B : Matrix I I ℝ) (ρ : J → I → ℝ) (c : I → J → ℝ)
    (B₀ C₀ : ℝ) (hC₀ : 1 ≤ C₀)
    (hB : ∀ i j, |B i j| ≤ B₀) (hρ : ∀ ν j, |ρ ν j| ≤ B₀)
    (hc : ∀ i ν, |c i ν| ≤ C₀) (ε : I → Option J) :
    |smoothCoefficient B ρ c ε| ≤
      C₀ ^ Fintype.card I * ((Fintype.card (Equiv.Perm I) : ℝ) * B₀ ^ Fintype.card I) := by
  rw [smoothCoefficient, abs_mul]
  exact mul_le_mul (abs_coefficient_product_le c C₀ hC₀ hc ε)
    (abs_det_le_card_perm _ B₀ (abs_selected_row_le B ρ B₀ hB hρ ε))
    (abs_nonneg _) (pow_nonneg (zero_le_one.trans hC₀) _)

omit [DecidableEq J] in
/-- Enlarge the actual distinct-selection sum to all finite selections and count them. -/
theorem coefficientBound_le_cardinality (B : Matrix I I ℝ) (ρ : J → I → ℝ) (c : I → J → ℝ)
    (B₀ C₀ : ℝ) (hB₀ : 1 ≤ B₀) (hC₀ : 1 ≤ C₀)
    (hB : ∀ i j, |B i j| ≤ B₀) (hρ : ∀ ν j, |ρ ν j| ≤ B₀)
    (hc : ∀ i ν, |c i ν| ≤ C₀) :
    coefficientBound B ρ c ≤ (Fintype.card (I → Option J) : ℝ) * C₀ ^ Fintype.card I *
      (Fintype.card (Equiv.Perm I) : ℝ) * B₀ ^ Fintype.card I := by
  classical
  let S := Finset.univ.filter (PoleDistinct (I := I) (J := J))
  let K := C₀ ^ Fintype.card I * ((Fintype.card (Equiv.Perm I) : ℝ) * B₀ ^ Fintype.card I)
  have hK : 0 ≤ K := mul_nonneg (pow_nonneg (zero_le_one.trans hC₀) _)
    (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (zero_le_one.trans hB₀) _))
  calc
    coefficientBound B ρ c ≤ ∑ _ε ∈ S, K :=
      Finset.sum_le_sum (fun ε _ ↦ abs_smoothCoefficient_le B ρ c B₀ C₀ hC₀ hB hρ hc ε)
    _ = (S.card : ℝ) * K := by simp
    _ ≤ (Fintype.card (I → Option J) : ℝ) * K := by
      apply mul_le_mul_of_nonneg_right _ hK
      exact_mod_cast (Finset.card_le_card (Finset.filter_subset _ _) :
        S.card ≤ (Finset.univ : Finset (I → Option J)).card)
    _ = _ := by dsimp [K]; ring

omit [DecidableEq J] in
/-- Closed-form numerical bound: at most `(card J + 1)^d` choices and `d!` permutation terms. -/
theorem coefficientBound_le_uniform (B : Matrix I I ℝ) (ρ : J → I → ℝ) (c : I → J → ℝ)
    (B₀ C₀ : ℝ) (hB₀ : 1 ≤ B₀) (hC₀ : 1 ≤ C₀)
    (hB : ∀ i j, |B i j| ≤ B₀) (hρ : ∀ ν j, |ρ ν j| ≤ B₀)
    (hc : ∀ i ν, |c i ν| ≤ C₀) :
    coefficientBound B ρ c ≤ ((Fintype.card J : ℝ) + 1) ^ Fintype.card I * C₀ ^ Fintype.card I *
      ((Fintype.card I).factorial : ℝ) * B₀ ^ Fintype.card I := by
  simpa only [Fintype.card_fun, Fintype.card_option, Fintype.card_perm,
    Nat.cast_pow, Nat.cast_add, Nat.cast_one] using
      coefficientBound_le_cardinality B ρ c B₀ C₀ hB₀ hC₀ hB hρ hc

end EnvelopingIsomorphism.Deformation.Kontsevich.RadialPoleDeterminant
