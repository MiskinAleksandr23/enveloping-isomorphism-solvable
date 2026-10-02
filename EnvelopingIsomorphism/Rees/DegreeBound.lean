import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.GradedMonoid
import Mathlib.LinearAlgebra.Span.Basic

/-!
Uniform coefficientwise degree bounds for substitutions into a filtered,
possibly noncommutative algebra. The bound at power-series order r is
n + r * C, uniformly over all products of n generators.

The concrete PBW filtration is supplied by a separate module.
-/

namespace EnvelopingIsomorphism.Rees

variable {k A : Type*} [CommSemiring k] [Semiring A] [Algebra k A]

/-- A series has degree at most n + r*C in its coefficient of order r. -/
def DegreeBound (F : ℕ → Submodule k A) (C n : ℕ) (f : PowerSeries A) : Prop :=
  ∀ r, PowerSeries.coeff r f ∈ F (n + r * C)

namespace DegreeBound

variable {F : ℕ → Submodule k A} {C n m : ℕ} {f g : PowerSeries A}

theorem zero : DegreeBound F C n 0 := by
  intro r
  simp

theorem add (hf : DegreeBound F C n f) (hg : DegreeBound F C n g) :
    DegreeBound F C n (f + g) := by
  intro r
  simpa using (F (n + r * C)).add_mem (hf r) (hg r)

theorem smul (a : k) (hf : DegreeBound F C n f) :
    DegreeBound F C n (a • f) := by
  intro r
  simpa using (F (n + r * C)).smul_mem a (hf r)

theorem mono (hF : Monotone F) (hn : n ≤ m) (hf : DegreeBound F C n f) :
    DegreeBound F C m f := by
  intro r
  exact hF (Nat.add_le_add_right hn _) (hf r)

theorem sum {ι : Type*} (s : Finset ι) (p : ι → PowerSeries A)
    (h : ∀ i ∈ s, DegreeBound F C n (p i)) :
    DegreeBound F C n (∑ i ∈ s, p i) := by
  intro r
  simpa using (F (n + r * C)).sum_mem (fun i hi => h i hi r)

theorem one [SetLike.GradedMonoid F] : DegreeBound F C 0 1 := by
  intro r
  by_cases hr : r = 0
  · subst r
    simpa using SetLike.one_mem_graded F
  · simp [PowerSeries.coeff_one, hr]

theorem mul [SetLike.GradedMonoid F]
    (hf : DegreeBound F C n f) (hg : DegreeBound F C m g) :
    DegreeBound F C (n + m) (f * g) := by
  intro r
  rw [PowerSeries.coeff_mul]
  apply Submodule.sum_mem
  intro p hp
  have hr : p.1 + p.2 = r := Finset.mem_antidiagonal.mp hp
  have h := SetLike.mul_mem_graded (hf p.1) (hg p.2)
  simpa only [← hr, Nat.add_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h

/-- Products of generator images satisfy a bound uniform in the input length. -/
theorem list_prod [SetLike.GradedMonoid F]
    (fs : List (PowerSeries A)) (h : ∀ f ∈ fs, DegreeBound F C 1 f) :
    DegreeBound F C fs.length fs.prod := by
  induction fs with
  | nil => simpa using (one (F := F) (C := C))
  | cons f fs ih =>
    have hf : DegreeBound F C 1 f := h f List.mem_cons_self
    have ht : DegreeBound F C fs.length fs.prod :=
      ih (fun g hg => h g (List.mem_cons_of_mem f hg))
    simpa [Nat.add_comm] using hf.mul ht

/-- A linear constant term and degree-D higher coefficients give excess D-1. -/
theorem of_generator_bound (hF : Monotone F) {D : ℕ} (hD : 1 ≤ D)
    (h₀ : PowerSeries.coeff 0 f ∈ F 1)
    (hpos : ∀ r, r ≠ 0 → PowerSeries.coeff r f ∈ F D) :
    DegreeBound F (D - 1) 1 f := by
  intro r
  cases r with
  | zero => simpa using h₀
  | succ r =>
    apply hF _ (hpos (r + 1) (Nat.succ_ne_zero r))
    simp only [Nat.add_mul, one_mul]
    omega

/-- The uniform estimate used in E2 before passing to symmetric PBW coordinates. -/
theorem product_generator_bound [SetLike.GradedMonoid F]
    (hF : Monotone F) {D : ℕ} (hD : 1 ≤ D)
    (fs : List (PowerSeries A))
    (h₀ : ∀ f ∈ fs, PowerSeries.coeff 0 f ∈ F 1)
    (hpos : ∀ f ∈ fs, ∀ r, r ≠ 0 → PowerSeries.coeff r f ∈ F D)
    (r : ℕ) :
    PowerSeries.coeff r fs.prod ∈ F (fs.length + r * (D - 1)) :=
  list_prod fs (fun f hf => of_generator_bound hF hD (h₀ f hf) (hpos f hf)) r

end DegreeBound

section ChangeOfCoordinates

variable {B : Type*} [Semiring B] [Algebra k B]

/-- Apply a nonnegative formal series of linear maps coefficientwise. -/
noncomputable def applyLinearSeries (T : ℕ → A →ₗ[k] B)
    (f : PowerSeries A) : PowerSeries B :=
  PowerSeries.mk fun r =>
    ∑ p ∈ Finset.antidiagonal r, T p.1 (PowerSeries.coeff p.2 f)

@[simp] theorem coeff_applyLinearSeries (T : ℕ → A →ₗ[k] B)
    (f : PowerSeries A) (r : ℕ) :
    PowerSeries.coeff r (applyLinearSeries T f) =
      ∑ p ∈ Finset.antidiagonal r, T p.1 (PowerSeries.coeff p.2 f) :=
  PowerSeries.coeff_mk r _

/-- Degree-nonincreasing changes of coordinates with nonnegative parameter
orders preserve the uniform excess bound. This includes the final
reordering and inverse symmetrization stages of E2 once their PBW estimates
have been established. -/
theorem DegreeBound.applyLinearSeries
    {F : ℕ → Submodule k A} {G : ℕ → Submodule k B} (hG : Monotone G)
    (T : ℕ → A →ₗ[k] B)
    (hT : ∀ i n x, x ∈ F n → T i x ∈ G n)
    {C n : ℕ} {f : PowerSeries A} (hf : DegreeBound F C n f) :
    DegreeBound G C n (applyLinearSeries T f) := by
  intro r
  rw [coeff_applyLinearSeries]
  apply Submodule.sum_mem
  intro p hp
  have hr : p.1 + p.2 = r := Finset.mem_antidiagonal.mp hp
  apply hG (Nat.add_le_add_left (Nat.mul_le_mul_right C (show p.2 ≤ r by omega)) n)
  exact hT p.1 (n + p.2 * C) (PowerSeries.coeff p.2 f) (hf p.2)

end ChangeOfCoordinates
end EnvelopingIsomorphism.Rees
