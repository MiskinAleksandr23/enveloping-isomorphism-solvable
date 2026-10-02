import EnvelopingIsomorphism.FormalSeries.LaurentBilinear
import EnvelopingIsomorphism.FormalSeries.PowerSeriesModule
import EnvelopingIsomorphism.FormalSeries.ArityAntidiagonal

/-! Genuine sums of all graph arities and uniform estimates for their tails.
Only each finite t-jet is bounded; no common h-bound over all t degrees is used. -/

noncomputable section

namespace EnvelopingIsomorphism.FormalSeries.LaurentAritySummation

open LaurentModule PowerSeriesModule
open scoped BigOperators Classical

universe u v
variable {k : Type u} [CommRing k] {V : Type v} [AddCommGroup V] [Module k V]

abbrev Series (k V : Type*) [CommRing k] [AddCommGroup V] [Module k V] :=
  PowerSeriesModule (LaurentSeries k) (LaurentModule k V)

def Summable (A : ℕ → Series k V) : Prop :=
  ∀ d, ∃ b : ℤ, ∀ m : ℕ, BoundedBelow ((m : ℤ) + b) (coeffV d (A m))

def jointSum (A : ℕ → Series k V) (d : ℕ) (h : ℤ) : V :=
  ∑ᶠ m : ℕ, coeff (coeffV d (A m)) h

theorem jointSum_eq_zero (A : ℕ → Series k V) (d : ℕ) (b : ℤ)
    (hA : ∀ m : ℕ, BoundedBelow ((m : ℤ) + b) (coeffV d (A m)))
    (h : ℤ) (hh : h < b) : jointSum A d h = 0 := by
  apply finsum_eq_zero_of_forall_eq_zero
  intro m
  exact hA m h (by omega)

def sumCoefficient (A : ℕ → Series k V) (hA : Summable A) (d : ℕ) : LaurentModule k V :=
  HahnModule.of k (HahnSeries.ofSuppBddBelow (jointSum A d) (by
    obtain ⟨b, hb⟩ := hA d
    refine ⟨b, ?_⟩
    intro h hh
    by_contra hn
    exact hh (jointSum_eq_zero A d b hb h (lt_of_not_ge hn))))

def sumSeries (A : ℕ → Series k V) (hA : Summable A) : Series k V :=
  PowerSeriesModule.mk (sumCoefficient A hA)

@[simp] theorem coeff_sumSeries (A : ℕ → Series k V) (hA : Summable A) (d : ℕ) (h : ℤ) :
    coeff (coeffV d (sumSeries A hA)) h = jointSum A d h := rfl

theorem sumSeries_bound (A : ℕ → Series k V) (hA : Summable A) (d : ℕ) (b : ℤ)
    (hb : ∀ m : ℕ, BoundedBelow ((m : ℤ) + b) (coeffV d (A m))) :
    BoundedBelow b (coeffV d (sumSeries A hA)) :=
  jointSum_eq_zero A d b hb

def truncate (A : ℕ → Series k V) (N : ℕ) : Series k V := ∑ m ∈ Finset.range N, A m

theorem coeff_finset_sum {ι : Type*} (s : Finset ι) (x : ι → LaurentModule k V) (h : ℤ) :
    coeff (∑ i ∈ s, x i) h = ∑ i ∈ s, coeff (x i) h := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih]

theorem jointSum_eq_truncate (A : ℕ → Series k V) (d : ℕ) (b : ℤ)
    (hb : ∀ m : ℕ, BoundedBelow ((m : ℤ) + b) (coeffV d (A m)))
    (N : ℕ) (h : ℤ) (hh : h < (N : ℤ) + b) :
    jointSum A d h = ∑ m ∈ Finset.range N, coeff (coeffV d (A m)) h := by
  apply finsum_eq_sum_of_support_subset
  intro m hm
  by_contra hn
  have hNm : N ≤ m := by simpa using hn
  exact hm (hb m h (by omega))

@[simp] theorem coeff_truncate (A : ℕ → Series k V) (N d : ℕ) (h : ℤ) :
    coeff (coeffV d (truncate A N)) h =
      ∑ m ∈ Finset.range N, coeff (coeffV d (A m)) h := by
  rw [truncate, coeffV_sum]
  have hc (s : Finset ℕ) : coeff (∑ m ∈ s, coeffV d (A m)) h =
      ∑ m ∈ s, coeff (coeffV d (A m)) h := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert m s hm ih => simp [hm, ih]
  exact hc _

/-- The omitted arities start at N+b, uniformly over their infinite tail. -/
theorem tail_bound (A : ℕ → Series k V) (hA : Summable A) (d : ℕ) (b : ℤ)
    (hb : ∀ m : ℕ, BoundedBelow ((m : ℤ) + b) (coeffV d (A m))) (N : ℕ) :
    BoundedBelow ((N : ℤ) + b) (coeffV d (sumSeries A hA - truncate A N)) := by
  intro h hh
  rw [coeffV_sub, coeff_sub, coeff_sumSeries, coeff_truncate,
    jointSum_eq_truncate A d b hb N h hh, sub_self]

theorem boundedBelow_finset_sum {ι : Type*} (s : Finset ι)
    (x : ι → LaurentModule k V) (b : ℤ) (hx : ∀ i ∈ s, BoundedBelow b (x i)) :
    BoundedBelow b (∑ i ∈ s, x i) := by
  induction s using Finset.induction_on with
  | empty => simp [BoundedBelow]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact boundedBelow_add (hx i (Finset.mem_insert_self _ _))
      (ih (fun j hj => hx j (Finset.mem_insert_of_mem hj)))

theorem truncate_bound (A : ℕ → Series k V) (d : ℕ) (b : ℤ)
    (hb : ∀ m : ℕ, BoundedBelow ((m : ℤ) + b) (coeffV d (A m))) (N : ℕ) :
    BoundedBelow b (coeffV d (truncate A N)) := by
  rw [truncate, coeffV_sum]
  apply boundedBelow_finset_sum
  intro m _ h hh
  exact hb m h (by omega)

section Bilinear

variable {W Z : Type v} [AddCommGroup W] [Module k W] [AddCommGroup Z] [Module k Z]

def bilinear (f : V →ₗ[k] W →ₗ[k] Z) :
    Series k V →ₗ[PowerSeries (LaurentSeries k)]
      Series k W →ₗ[PowerSeries (LaurentSeries k)] Series k Z :=
  PowerSeriesModule.extendBilinear (LaurentModule.extendBilinear f)

theorem bilinear_bound (f : V →ₗ[k] W →ₗ[k] Z) (P : Series k V) (Q : Series k W)
    (D : ℕ) (b c K : ℤ)
    (hP : ∀ d ≤ D, BoundedBelow (b + (d : ℤ) * K) (coeffV d P))
    (hQ : ∀ d ≤ D, BoundedBelow (c + (d : ℤ) * K) (coeffV d Q)) :
    BoundedBelow (b + c + (D : ℤ) * K) (coeffV D (bilinear f P Q)) := by
  change BoundedBelow _ (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal D,
    LaurentModule.extendBilinear f (coeffV ij.1 P) (coeffV ij.2 Q))
  apply boundedBelow_finset_sum
  intro ij hij
  have hsum : ij.1 + ij.2 = D := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  have hp := hP ij.1 (by omega)
  have hq := hQ ij.2 (by omega)
  have h := boundedBelow_extendBilinear f _ _ hp hq
  have he : (b + (ij.1 : ℤ) * K) + (c + (ij.2 : ℤ) * K) = b + c + (D : ℤ) * K := by
    rw [← hsum, Nat.cast_add]
    ring
  rwa [he] at h

/-- Infinite arity sums may be replaced by finite sums before bilinear
composition, at every fixed joint coefficient. -/
theorem bilinear_coeff_eq_truncations (f : V →ₗ[k] W →ₗ[k] Z)
    (A : ℕ → Series k V) (B : ℕ → Series k W) (hA : Summable A) (hB : Summable B)
    (D : ℕ) (H K : ℤ)
    (hAb : ∀ d ≤ D, ∀ m : ℕ, BoundedBelow ((m : ℤ) + (d : ℤ) * K) (coeffV d (A m)))
    (hBb : ∀ d ≤ D, ∀ m : ℕ, BoundedBelow ((m : ℤ) + (d : ℤ) * K) (coeffV d (B m)))
    (N : ℕ) (hN : H < (N : ℤ) + (D : ℤ) * K) :
    coeff (coeffV D (bilinear f (sumSeries A hA) (sumSeries B hB))) H =
      coeff (coeffV D (bilinear f (truncate A N) (truncate B N))) H := by
  have hid : bilinear f (sumSeries A hA) (sumSeries B hB) -
      bilinear f (truncate A N) (truncate B N) =
        bilinear f (sumSeries A hA - truncate A N) (sumSeries B hB) +
          bilinear f (truncate A N) (sumSeries B hB - truncate B N) := by
    simp only [map_sub, LinearMap.sub_apply]
    abel
  have hleft : BoundedBelow ((N : ℤ) + (D : ℤ) * K)
      (coeffV D (bilinear f (sumSeries A hA - truncate A N) (sumSeries B hB))) := by
    apply bilinear_bound f _ _ D (N : ℤ) 0 K
    · intro d hd
      exact tail_bound A hA d _ (hAb d hd) N
    · intro d hd
      simpa only [zero_add] using sumSeries_bound B hB d _ (hBb d hd)
  have hright : BoundedBelow ((N : ℤ) + (D : ℤ) * K)
      (coeffV D (bilinear f (truncate A N) (sumSeries B hB - truncate B N))) := by
    simpa only [zero_add] using bilinear_bound f (truncate A N)
      (sumSeries B hB - truncate B N) D 0 (N : ℤ) K
      (fun d hd => by simpa only [zero_add] using truncate_bound A d _ (hAb d hd) N)
      (fun d hd => tail_bound B hB d _ (hBb d hd) N)
  have he : BoundedBelow ((N : ℤ) + (D : ℤ) * K)
      (coeffV D (bilinear f (sumSeries A hA) (sumSeries B hB) -
        bilinear f (truncate A N) (truncate B N))) := by
    rw [hid, coeffV_add]
    exact boundedBelow_add hleft hright
  have hz := he H hN
  rw [coeffV_sub, coeff_sub] at hz
  exact sub_eq_zero.mp hz

/-- Exact all-arity Fubini at each joint coefficient, with a finite total-arity
cutoff justified by the actual Laurent lower bounds. -/
theorem bilinear_coeff_eq_total_arities (f : V →ₗ[k] W →ₗ[k] Z)
    (A : ℕ → Series k V) (B : ℕ → Series k W) (hA : Summable A) (hB : Summable B)
    (D : ℕ) (H K : ℤ)
    (hAb : ∀ d ≤ D, ∀ m : ℕ, BoundedBelow ((m : ℤ) + (d : ℤ) * K) (coeffV d (A m)))
    (hBb : ∀ d ≤ D, ∀ m : ℕ, BoundedBelow ((m : ℤ) + (d : ℤ) * K) (coeffV d (B m)))
    (N : ℕ) (hN : H < (N : ℤ) + (D : ℤ) * K) :
    coeff (coeffV D (bilinear f (sumSeries A hA) (sumSeries B hB))) H =
      ∑ m ∈ Finset.range N, ∑ p ∈ Finset.HasAntidiagonal.antidiagonal m,
        coeff (coeffV D (bilinear f (A p.1) (B p.2))) H := by
  rw [bilinear_coeff_eq_truncations f A B hA hB D H K hAb hBb N hN]
  simp only [truncate, map_sum, LinearMap.sum_apply, coeffV_sum, coeff_finset_sum]
  rw [Finset.sum_comm]
  refine ArityAntidiagonal.sum_range_square_eq_sum_antidiagonal N
    (fun a b : ℕ => coeff (coeffV D (bilinear f (A a) (B b))) H) ?_
  intro a b hab
  have hbnd := bilinear_bound f (A a) (B b) D (a : ℤ) (b : ℤ) K
    (fun d hd => hAb d hd a) (fun d hd => hBb d hd b)
  apply hbnd H
  omega

/-- A proved homogeneous bilinear identity survives the genuine all-arity
completion. Only finite-jet slopes, never one global h-bound, are required. -/
theorem bilinear_self_eq_zero_of_homogeneous (f : V →ₗ[k] V →ₗ[k] Z)
    (A : ℕ → Series k V) (hA : Summable A)
    (hlocal : ∀ D : ℕ, ∃ K : ℤ, ∀ d ≤ D, ∀ m : ℕ,
      BoundedBelow ((m : ℤ) + (d : ℤ) * K) (coeffV d (A m)))
    (hhom : ∀ m, ∑ p ∈ Finset.HasAntidiagonal.antidiagonal m,
      bilinear f (A p.1) (A p.2) = 0) :
    bilinear f (sumSeries A hA) (sumSeries A hA) = 0 := by
  apply PowerSeriesModule.ext
  intro D
  apply LaurentModule.ext
  intro H
  obtain ⟨K, hK⟩ := hlocal D
  let N := (H - (D : ℤ) * K).toNat + 1
  have hN : H < (N : ℤ) + (D : ℤ) * K := by dsimp [N]; omega
  rw [bilinear_coeff_eq_total_arities f A A hA hA D H K hK hK N hN,
    coeffV_zero, coeff_zero]
  apply Finset.sum_eq_zero
  intro m _
  have h := congrArg (fun P : Series k Z => coeff (coeffV D P) H) (hhom m)
  simpa only [coeffV_sum, coeff_finset_sum, coeffV_zero, coeff_zero] using h

end Bilinear

end EnvelopingIsomorphism.FormalSeries.LaurentAritySummation
