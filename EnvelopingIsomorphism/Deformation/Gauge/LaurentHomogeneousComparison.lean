import EnvelopingIsomorphism.FormalSeries.LaurentAritySummation

/-! A coefficientwise homogeneous identity determines the actual full
bilinear operation, with only finite-jet bounds on both arity families. -/

noncomputable section
namespace EnvelopingIsomorphism.Deformation.Gauge.LaurentHomogeneousComparison
open EnvelopingIsomorphism.FormalSeries LaurentAritySummation
open scoped BigOperators Classical

universe u v
variable {k : Type u} [CommRing k] {U V W : Type v}
  [AddCommGroup U] [Module k U] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W]

def homogeneousTerm (Q : U →ₗ[k] V →ₗ[k] W)
    (A : ℕ → Series k U) (B : ℕ → Series k V) (N : ℕ) : Series k W :=
  ∑ p ∈ Finset.HasAntidiagonal.antidiagonal N, bilinear Q (A p.1) (B p.2)

theorem homogeneousTerm_bound (Q : U →ₗ[k] V →ₗ[k] W)
    (A : ℕ → Series k U) (B : ℕ → Series k V) (D N : ℕ) (K : ℤ)
    (hA : ∀ e ≤ D, ∀ m : ℕ, LaurentModule.BoundedBelow ((m : ℤ) + (e : ℤ) * K)
      (PowerSeriesModule.coeffV e (A m)))
    (hB : ∀ e ≤ D, ∀ m : ℕ, LaurentModule.BoundedBelow ((m : ℤ) + (e : ℤ) * K)
      (PowerSeriesModule.coeffV e (B m))) :
    LaurentModule.BoundedBelow ((N : ℤ) + (D : ℤ) * K)
      (PowerSeriesModule.coeffV D (homogeneousTerm Q A B N)) := by
  rw [homogeneousTerm, PowerSeriesModule.coeffV_sum]
  apply boundedBelow_finset_sum
  intro p hp
  have he : p.1 + p.2 = N := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  have hb := bilinear_bound Q (A p.1) (B p.2) D (p.1 : ℤ) (p.2 : ℤ) K
    (fun e he ↦ hA e he p.1) (fun e he ↦ hB e he p.2)
  simpa only [← Nat.cast_add, he] using hb

/-- The finite total-arity support justifies the full product comparison.
The supplied coefficient identity is an algebraic equality, not a convergence
assumption, and all summation tails are explicitly proved to vanish. -/
theorem eq_bilinear_of_coeff_homogeneous
    (Q : U →ₗ[k] V →ₗ[k] W)
    (A : ℕ → Series k U) (B : ℕ → Series k V) (hA : Summable A) (hB : Summable B)
    (hlocal : ∀ D : ℕ, ∃ K : ℤ,
      (∀ e ≤ D, ∀ m : ℕ, LaurentModule.BoundedBelow ((m : ℤ) + (e : ℤ) * K)
        (PowerSeriesModule.coeffV e (A m))) ∧
      (∀ e ≤ D, ∀ m : ℕ, LaurentModule.BoundedBelow ((m : ℤ) + (e : ℤ) * K)
        (PowerSeriesModule.coeffV e (B m))))
    (P : Series k W)
    (hP : ∀ (D : ℕ) (H : ℤ), LaurentModule.coeff (PowerSeriesModule.coeffV D P) H =
      ∑ᶠ N : ℕ, LaurentModule.coeff (PowerSeriesModule.coeffV D (homogeneousTerm Q A B N)) H) :
    P = bilinear Q (sumSeries A hA) (sumSeries B hB) := by
  apply PowerSeriesModule.ext
  intro D
  apply LaurentModule.ext
  intro H
  obtain ⟨K, hAK, hBK⟩ := hlocal D
  let M := (H - (D : ℤ) * K).toNat + 1
  have hM : H < (M : ℤ) + (D : ℤ) * K := by dsimp [M]; omega
  rw [hP D H, bilinear_coeff_eq_total_arities Q A B hA hB D H K hAK hBK M hM]
  calc
    _ = ∑ N ∈ Finset.range M,
        LaurentModule.coeff (PowerSeriesModule.coeffV D (homogeneousTerm Q A B N)) H := by
      apply finsum_eq_sum_of_support_subset
      intro N hN
      by_contra hn
      have hNM : M ≤ N := by simpa using hn
      exact hN (homogeneousTerm_bound Q A B D N K hAK hBK H (by omega))
    _ = _ := by
      simp only [homogeneousTerm, PowerSeriesModule.coeffV_sum, coeff_finset_sum]

end EnvelopingIsomorphism.Deformation.Gauge.LaurentHomogeneousComparison
