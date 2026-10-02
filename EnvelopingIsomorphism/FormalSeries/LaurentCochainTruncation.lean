import EnvelopingIsomorphism.FormalSeries.Multilinear

/-! Actual head/tail reindexing and finite nonnegative-cochain truncation of Laurent convolution. -/

noncomputable section

namespace EnvelopingIsomorphism.FormalSeries.LaurentModule

open scoped BigOperators Classical

universe u v
variable {k : Type u} [CommRing k] {V W : Type v}
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

/-- Split the genuine `(r+1)`-tuple coefficient convolution into the cochain
exponent and the r input exponents. Both sums have their actual finite support. -/
theorem coeff_extendCochain_eq_finsum (r : ℕ) (F : LaurentModule k (Cochain k V W r))
    (x : Fin r → LaurentModule k V) (H : ℤ) :
    coeff (extendCochain r F x) H =
      ∑ᶠ j : ℤ, coeff (applyMultilinear (coeff F j) x) (H - j) := by
  let g : (Fin (r + 1) → ℤ) → W := fun q =>
    if ∑ i, q i = H then (coeff F (q 0)) (fun i => coeff (x i) (q i.succ)) else 0
  let E : (ℤ × (Fin r → ℤ)) ≃ (Fin (r + 1) → ℤ) := Fin.consEquiv (fun _ => ℤ)
  have hfinite : Function.HasFiniteSupport (g ∘ E) :=
    (finite_support_extendCochain r F x H).comp_of_injective E.injective
  rw [coeff_extendCochain]
  change (∑ᶠ q, g q) = _
  calc
    (∑ᶠ q, g q) = ∑ᶠ p, g (E p) := (finsum_comp_equiv E).symm
    _ = ∑ᶠ j : ℤ, ∑ᶠ q : Fin r → ℤ, g (E (j, q)) := finsum_curry (g ∘ E) hfinite
    _ = _ := by
      apply finsum_congr
      intro j
      rw [coeff_applyMultilinear, convolutionCoeff]
      apply finsum_congr
      intro q
      change (if ∑ i, (Fin.cons j q) i = H then
        (coeff F j) (fun i => coeff (x i) (q i)) else 0) = term (coeff F j) x (H - j) q
      simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, term]
      have he : j + ∑ i, q i = H ↔ ∑ i, q i = H - j := by omega
      simp only [he]

/-- Negative cochain exponents contribute zero for a genuinely nonnegative cochain series. -/
theorem coeff_apply_cochain_eq_zero_of_neg {r : ℕ}
    (F : LaurentModule k (Cochain k V W r)) (hF : BoundedBelow 0 F)
    (x : Fin r → LaurentModule k V) (H j : ℤ) (hj : j < 0) :
    coeff (applyMultilinear (coeff F j) x) (H - j) = 0 := by
  rw [hF j hj]
  simp [coeff_applyMultilinear, convolutionCoeff, term]

/-- Input lower bounds force the actual upper bound on contributing cochain exponents. -/
theorem coeff_apply_cochain_eq_zero_above_cutoff {r : ℕ}
    (F : LaurentModule k (Cochain k V W r)) (x : Fin r → LaurentModule k V)
    (L : Fin r → ℤ) (hx : ∀ i, BoundedBelow (L i) (x i))
    (H j : ℤ) (hj : H - ∑ i, L i < j) :
    coeff (applyMultilinear (coeff F j) x) (H - j) = 0 :=
  boundedBelow_applyMultilinear (coeff F j) x hx (H - j) (by omega)

/-- The actual head-coefficient support lies in the finite integer interval. -/
theorem support_cochain_head_subset {r : ℕ}
    (F : LaurentModule k (Cochain k V W r)) (hF : BoundedBelow 0 F)
    (x : Fin r → LaurentModule k V) (L : Fin r → ℤ)
    (hx : ∀ i, BoundedBelow (L i) (x i)) (H : ℤ) :
    Function.support (fun j : ℤ => coeff (applyMultilinear (coeff F j) x) (H - j)) ⊆
      (Finset.Icc 0 (H - ∑ i, L i) : Finset ℤ) := by
  intro j hj
  change coeff (applyMultilinear (coeff F j) x) (H - j) ≠ 0 at hj
  simp only [Finset.mem_coe, Finset.mem_Icc]
  constructor
  · by_contra h
    exact hj (coeff_apply_cochain_eq_zero_of_neg F hF x H j (lt_of_not_ge h))
  · by_contra h
    exact hj (coeff_apply_cochain_eq_zero_above_cutoff F x L hx H j (lt_of_not_ge h))

/-- Exact integer-interval truncation; the interval is empty when H is below the
sum of the input bounds. No cochain expansion is assumed. -/
theorem coeff_extendCochain_nonnegative_Icc (r : ℕ)
    (F : LaurentModule k (Cochain k V W r)) (hF : BoundedBelow 0 F)
    (x : Fin r → LaurentModule k V) (L : Fin r → ℤ)
    (hx : ∀ i, BoundedBelow (L i) (x i)) (H : ℤ) :
    coeff (extendCochain r F x) H =
      ∑ j ∈ Finset.Icc 0 (H - ∑ i, L i), coeff (applyMultilinear (coeff F j) x) (H - j) := by
  rw [coeff_extendCochain_eq_finsum]
  exact finsum_eq_sum_of_support_subset _ (support_cochain_head_subset F hF x L hx H)

/-- Natural-index truncation for the actual Laurent action. If the integer cutoff
is negative, the displayed j=0 term vanishes by the genuine input lower bounds. -/
theorem coeff_extendCochain_nonnegative (r : ℕ)
    (F : LaurentModule k (Cochain k V W r)) (hF : BoundedBelow 0 F)
    (x : Fin r → LaurentModule k V) (L : Fin r → ℤ)
    (hx : ∀ i, BoundedBelow (L i) (x i)) (H : ℤ) :
    coeff (extendCochain r F x) H =
      ∑ j ∈ Finset.range ((H - ∑ i, L i).toNat + 1),
        coeff (applyMultilinear (coeff F (j : ℤ)) x) (H - j) := by
  let e : ℕ ↪ ℤ := ⟨Int.ofNat, Int.ofNat_injective⟩
  have hs : Function.support (fun j : ℤ => coeff (applyMultilinear (coeff F j) x) (H - j)) ⊆
      (Finset.range ((H - ∑ i, L i).toNat + 1)).map e := by
    intro j hj
    have hb := support_cochain_head_subset F hF x L hx H hj
    simp only [Finset.mem_coe, Finset.mem_Icc] at hb
    apply Finset.mem_map.mpr
    refine ⟨j.toNat, ?_, Int.toNat_of_nonneg hb.1⟩
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Int.toNat_le_toNat hb.2))
  rw [coeff_extendCochain_eq_finsum, finsum_eq_sum_of_support_subset _ hs, Finset.sum_map]
  rfl

end EnvelopingIsomorphism.FormalSeries.LaurentModule
