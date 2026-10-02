import EnvelopingIsomorphism.Deformation.Polyvectors

/-! Coordinate evaluation formulas for arbitrary polynomial multiderivations.
The coefficients are arbitrary polynomials, with no linear-degree restriction.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Multiderivation

open MvPolynomial

variable {K : Type*} [CommRing K]

private theorem derivation_sum_apply {ι σ : Type*} (s : Finset ι)
    (D : ι → Derivation K (MvPolynomial σ K) (MvPolynomial σ K)) (p : MvPolynomial σ K) :
    (∑ i ∈ s, D i) p = ∑ i ∈ s, D i p := by
  have h := congrFun (map_sum Derivation.coeFnAddMonoidHom D s) p
  simpa only [Derivation.coeFnAddMonoidHom_apply, Finset.sum_apply] using h

/-- Every polynomial derivation is its actual sum of coordinate partial derivatives. -/
theorem derivation_coordinate_expansion {σ : Type*} [Fintype σ]
    (D : Derivation K (MvPolynomial σ K) (MvPolynomial σ K)) :
    D = ∑ i : σ, D (X i) • pderiv i := by
  classical
  apply MvPolynomial.derivation_ext
  intro j
  rw [derivation_sum_apply]
  simp [Derivation.smul_apply, pderiv_X, Pi.single_apply, smul_eq_mul]

theorem derivation_apply_coordinate_expansion {σ : Type*} [Fintype σ]
    (D : Derivation K (MvPolynomial σ K) (MvPolynomial σ K)) (p : MvPolynomial σ K) :
    D p = ∑ i : σ, D (X i) * pderiv i p := by
  have h := congrArg (fun T : Derivation K (MvPolynomial σ K) (MvPolynomial σ K) ↦ T p)
    (derivation_coordinate_expansion D)
  simpa only [derivation_sum_apply, Derivation.smul_apply, smul_eq_mul] using h

/-- Arbitrary arity, including zero: one coordinate choice per input slot.
This is the coefficient product formula used by the actual one-vertex graph contraction. -/
theorem apply_coordinate_expansion {σ : Type*} [Fintype σ] (r : ℕ)
    (F : Multiderivation K (MvPolynomial σ K) r) (f : Fin r → MvPolynomial σ K) :
    F f = ∑ lab : Fin r → σ,
      F (fun i ↦ X (lab i)) * ∏ i : Fin r, pderiv (lab i) (f i) := by
  classical
  induction r with
  | zero =>
    simp only [Fin.prod_univ_zero, mul_one, Fintype.sum_unique]
    congr 1
    exact Subsingleton.elim _ _
  | succ r ih =>
    have hd := derivation_apply_coordinate_expansion (F.slotDerivation 0 f) (f 0)
    simp only [slotDerivation_apply, Function.update_eq_self] at hd
    rw [hd]
    have hupdate (i : σ) : Function.update f 0 (X i) = Fin.cons (X i) (Fin.tail f) := by
      nth_rw 1 [← Fin.cons_self_tail f]
      rw [Fin.update_cons_zero]
    simp only [hupdate, ← curryLeft_apply]
    have hexp (i : σ) := ih (F.curryLeft (X i)) (Fin.tail f)
    simp_rw [hexp, Finset.sum_mul]
    rw [← (Fin.consEquiv (fun _ : Fin (r + 1) ↦ σ)).sum_comp]
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro lab hlab
    simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
      curryLeft_apply, Fin.tail_def]
    have hc : (fun j : Fin (r + 1) ↦ (X ((Fin.cons i lab : Fin (r + 1) → σ) j) : MvPolynomial σ K)) =
        Fin.cons (X i : MvPolynomial σ K) (fun j : Fin r ↦ X (lab j)) := by
      funext j
      cases j using Fin.cases <;> rfl
    rw [hc]
    ring

end EnvelopingIsomorphism.Deformation.Multiderivation
