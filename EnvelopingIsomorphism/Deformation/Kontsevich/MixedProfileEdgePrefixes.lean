import EnvelopingIsomorphism.Deformation.GeneralGraphTwoOddProfiles
import EnvelopingIsomorphism.Deformation.Kontsevich.GraphEdgeOrder

/-! Literal vertex-major edge positions for mixed profiles. Additive formulas
retain the vector deficit without truncated natural subtraction. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.MixedProfileEdgePrefixes
open scoped Classical BigOperators
open KontsevichGraph.General
variable {n : ℕ}

theorem vectorArity_add_indicator (i u : Fin n) :
    oneExceptionalArity 1 i u + (if u = i then 1 else 0) = 2 := by
  by_cases h : u = i <;> simp [oneExceptionalArity, h]

theorem twoOddArity_add_indicator (i j : Fin n) (hji : j ≠ i) (u : Fin n) :
    twoOddArity i j u + (if u = i then 1 else 0) = 2 + (if u = j then 1 else 0) := by
  by_cases hi : u = i
  · subst u
    simp [twoOddArity, hji.symm]
  · by_cases hj : u = j <;> simp [twoOddArity, hi, hj, hji]

theorem sum_vectorArity_add_one (i : Fin n) :
    (∑ u, oneExceptionalArity 1 i u) + 1 = 2 * n := by
  have h := congrArg (fun f : Fin n → ℕ ↦ ∑ u, f u)
    (funext (vectorArity_add_indicator i))
  simpa only [Finset.sum_add_distrib, Fintype.sum_ite_eq', Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, Nat.mul_comm] using h

theorem sum_twoOddArity (i j : Fin n) (hji : j ≠ i) :
    (∑ u, twoOddArity i j u) = 2 * n := by
  have h := congrArg (fun f : Fin n → ℕ ↦ ∑ u, f u)
    (funext (twoOddArity_add_indicator i j hji))
  simp only [Finset.sum_add_distrib, Fintype.sum_ite_eq', Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h
  omega

theorem edgePrefix_vector_add (i w : Fin n) :
    edgePrefix (oneExceptionalArity 1 i) w + (if i < w then 1 else 0) = 2 * w.val := by
  have h (u : Fin n) :
      (if u < w then oneExceptionalArity 1 i u else 0) +
        (if u = i then (if i < w then 1 else 0) else 0) = if u < w then 2 else 0 := by
    by_cases hu : u = i
    · subst u
      by_cases hi : i < w <;> simp [oneExceptionalArity, hi]
    · by_cases hw : u < w <;> simp [oneExceptionalArity, hu, hw]
  have hh := congrArg (fun f : Fin n → ℕ ↦ ∑ u, f u) (funext h)
  simpa only [edgePrefix, Finset.sum_add_distrib, Fintype.sum_ite_eq',
    ← edgePrefix_constant 2 w] using hh

theorem edgePrefix_twoOdd_add (i j : Fin n) (hji : j ≠ i) (w : Fin n) :
    edgePrefix (twoOddArity i j) w + (if i < w then 1 else 0) =
      2 * w.val + (if j < w then 1 else 0) := by
  have h (u : Fin n) :
      (if u < w then twoOddArity i j u else 0) +
        (if u = i then (if i < w then 1 else 0) else 0) =
      (if u < w then 2 else 0) +
        (if u = j then (if j < w then 1 else 0) else 0) := by
    by_cases hu : u = i
    · subst u
      by_cases hi : i < w <;> simp [twoOddArity, hi, hji.symm]
    · by_cases hj : u = j
      · subst u
        by_cases hjw : j < w <;> simp [twoOddArity, hji, hjw]
      · by_cases hw : u < w <;> simp [twoOddArity, hu, hj, hw]
  have hh := congrArg (fun f : Fin n → ℕ ↦ ∑ u, f u) (funext h)
  simpa only [edgePrefix, Finset.sum_add_distrib, Fintype.sum_ite_eq',
    ← edgePrefix_constant 2 w] using hh

theorem edgePrefix_vector (i w : Fin n) :
    edgePrefix (oneExceptionalArity 1 i) w = 2 * w.val - (if i < w then 1 else 0) := by
  have h := edgePrefix_vector_add i w
  omega

theorem edgePrefix_twoOdd (i j : Fin n) (hji : j ≠ i) (w : Fin n) :
    edgePrefix (twoOddArity i j) w =
      2 * w.val + (if j < w then 1 else 0) - (if i < w then 1 else 0) := by
  have h := edgePrefix_twoOdd_add i j hji w
  omega

theorem twoOdd_rootPrefix_add (i j : Fin n) (hji : j ≠ i) :
    edgePrefix (twoOddArity i j) j + (if i < j then 1 else 0) = 2 * j.val := by
  simpa using edgePrefix_twoOdd_add i j hji j

theorem twoOdd_rootPrefix_sign (i j : Fin n) (hji : j ≠ i) :
    (-1 : ℤˣ) ^ edgePrefix (twoOddArity i j) j = -twoOddPlacementSign i j := by
  have h := congrArg (fun t : ℕ ↦ (-1 : ℤˣ)^t) (twoOdd_rootPrefix_add i j hji)
  rw [pow_add, pow_mul] at h
  norm_num only [even_two, Even.neg_pow, one_pow] at h
  by_cases hij : i < j
  · simp only [if_pos hij, pow_one, mul_neg_one, neg_eq_iff_eq_neg] at h
    simpa only [twoOddPlacementSign, if_pos hij] using h
  · simp only [if_neg hij, pow_zero, mul_one] at h
    simpa only [twoOddPlacementSign, if_neg hij, neg_neg] using h

theorem vectorOrder_symm_val_add (i : Fin n) (e : KontsevichGraph.General.Edge (oneExceptionalArity 1 i)) :
    ((vertexMajorEdgeEquiv (oneExceptionalArity 1 i)).symm e).val +
      (if i < e.1 then 1 else 0) = 2 * e.1.val + e.2.val := by
  rw [← Sigma.eta e, vertexMajorEdgeEquiv_symm_val]
  simp only [Sigma.fst, Sigma.snd]
  have h := edgePrefix_vector_add i e.1
  omega

theorem twoOddOrder_symm_val_add (i j : Fin n) (hji : j ≠ i)
    (e : KontsevichGraph.General.Edge (twoOddArity i j)) :
    ((vertexMajorEdgeEquiv (twoOddArity i j)).symm e).val +
      (if i < e.1 then 1 else 0) =
        2 * e.1.val + (if j < e.1 then 1 else 0) + e.2.val := by
  rw [← Sigma.eta e, vertexMajorEdgeEquiv_symm_val]
  simp only [Sigma.fst, Sigma.snd]
  have h := edgePrefix_twoOdd_add i j hji e.1
  omega

end EnvelopingIsomorphism.Deformation.Kontsevich.MixedProfileEdgePrefixes
