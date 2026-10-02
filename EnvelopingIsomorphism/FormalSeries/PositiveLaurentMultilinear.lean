import EnvelopingIsomorphism.Deformation.MiddleExactPerturbation

/-! The canonical positive-series embedding preserves arbitrary finite-arity
multilinear convolution in the actual Laurent modules. -/

noncomputable section

namespace EnvelopingIsomorphism.FormalSeries.PositiveLaurent

open EnvelopingIsomorphism.Deformation.MiddleExactPerturbation
open PowerSeriesModule
open scoped BigOperators

universe u v w
variable {k : Type u} [Field k]
variable {X : Type v} [AddCommGroup X] [Module k X]

/-- The existing zero-negative-coefficient embedding, bundled linearly over k. -/
def toLaurentLinear : PowerSeriesModule k X →ₗ[k] LaurentModule k X where
  toFun := toLaurent
  map_add' x y := by
    apply LaurentModule.ext
    intro d
    by_cases hd : 0 ≤ d
    · lift d to ℕ using hd
      simp
    · simp only [coeff_toLaurent_neg _ _ (lt_of_not_ge hd), LaurentModule.coeff_add, add_zero]
  map_smul' c x := by
    apply LaurentModule.ext
    intro d
    by_cases hd : 0 ≤ d
    · lift d to ℕ using hd
      simp
    · simp only [coeff_toLaurent_neg _ _ (lt_of_not_ge hd), LaurentModule.coeff_smul, smul_zero,
        RingHom.id_apply]

@[simp] theorem toLaurentLinear_apply (x : PowerSeriesModule k X) :
    toLaurentLinear x = toLaurent x := rfl

private def natTupleEmbedding (ι : Type*) : (ι → ℕ) ↪ (ι → ℤ) where
  toFun a i := (a i : ℤ)
  inj' _a _b h := funext fun i ↦ Int.ofNat_inj.mp (congrFun h i)

variable {ι : Type w} [Fintype ι]
variable {M : ι → Type v} [∀ i, AddCommGroup (M i)] [∀ i, Module k (M i)]
variable {N : Type v} [AddCommGroup N] [Module k N]

/-- Equality of the actual positive and Laurent multilinear evaluations. -/
theorem toLaurent_applyMultilinear (f : MultilinearMap k M N)
    (x : ∀ i, PowerSeriesModule k (M i)) :
    toLaurent (applyMultilinear f x) = LaurentModule.applyMultilinear f (fun i ↦ toLaurent (x i)) := by
  classical
  apply LaurentModule.ext
  intro d
  by_cases hd : 0 ≤ d
  · lift d to ℕ using hd
    rw [coeff_toLaurent_nat, coeffV_applyMultilinear, LaurentModule.coeff_applyMultilinear]
    let g : (ι → ℤ) → N := fun a ↦
      if ∑ i, a i = (d : ℤ) then f (fun i ↦ LaurentModule.coeff (toLaurent (x i)) (a i)) else 0
    have hs : Function.support g ⊆
        ↑((Finset.piAntidiag Finset.univ d).map (natTupleEmbedding ι)) := by
      intro a ha
      change g a ≠ 0 at ha
      have hsum : ∑ i, a i = (d : ℤ) := by
        by_contra h
        exact ha (if_neg h)
      change (if ∑ i, a i = (d : ℤ) then _ else 0) ≠ 0 at ha
      rw [if_pos hsum] at ha
      have hnonneg (i : ι) : 0 ≤ a i := by
        by_contra h
        exact ha (f.map_coord_zero i (coeff_toLaurent_neg (x i) (a i) (lt_of_not_ge h)))
      let b : ι → ℕ := fun i ↦ (a i).toNat
      have hb : (fun i ↦ (b i : ℤ)) = a := funext fun i ↦ Int.toNat_of_nonneg (hnonneg i)
      apply Finset.mem_map.mpr
      refine ⟨b, ?_, hb⟩
      apply Finset.mem_piAntidiag.mpr
      refine ⟨?_, by simp⟩
      have hbtotal : ∑ i, (b i : ℤ) = (d : ℤ) := by rw [hb]; exact hsum
      exact_mod_cast hbtotal
    change (∑ a ∈ Finset.piAntidiag Finset.univ d, f (fun i ↦ coeffV (a i) (x i))) = ∑ᶠ a, g a
    rw [finsum_eq_sum_of_support_subset g hs, Finset.sum_map]
    apply Finset.sum_congr rfl
    intro a ha
    have hsum : ∑ i, (a i : ℤ) = (d : ℤ) := by
      exact_mod_cast (Finset.mem_piAntidiag.mp ha).1
    simp [g, natTupleEmbedding, hsum]
  · have hd' := lt_of_not_ge hd
    rw [coeff_toLaurent_neg _ _ hd']
    exact (LaurentModule.boundedBelow_applyMultilinear f (fun i ↦ toLaurent (x i))
      (b := fun _ ↦ 0) (fun i ↦ toLaurent_boundedBelow (x i)) d (by simpa using hd')).symm

end EnvelopingIsomorphism.FormalSeries.PositiveLaurent
