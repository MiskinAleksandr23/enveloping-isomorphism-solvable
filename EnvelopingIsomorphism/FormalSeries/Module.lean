import Mathlib.RingTheory.LaurentSeries
import Mathlib.LinearAlgebra.Multilinear.Basic

/-! Laurent series of vectors, with a common lower bound on all coefficients.

The scalar action is convolution by Laurent series of scalars. No finite-dimensionality
assumption is made and no identification with an algebraic tensor product is used.
-/

noncomputable section

namespace EnvelopingIsomorphism.FormalSeries

abbrev LaurentModule (k X : Type*) [Semiring k] [AddCommMonoid X] [Module k X] :=
  HahnModule ℤ k X

variable {k X Y Z : Type*} [CommRing k]
  [AddCommGroup X] [Module k X]
  [AddCommGroup Y] [Module k Y]
  [AddCommGroup Z] [Module k Z]

namespace LaurentModule

/-- The coefficient vector at an integer exponent. -/
def coeff (x : LaurentModule k X) (d : ℤ) : X := ((HahnModule.of k).symm x).coeff d

@[ext] theorem ext {x y : LaurentModule k X} (h : ∀ d, coeff x d = coeff y d) : x = y :=
  HahnModule.ext _ _ (funext h)

@[simp] theorem coeff_zero (d : ℤ) : coeff (0 : LaurentModule k X) d = 0 := rfl
@[simp] theorem coeff_add (x y : LaurentModule k X) (d : ℤ) :
    coeff (x + y) d = coeff x d + coeff y d := rfl
@[simp] theorem coeff_neg (x : LaurentModule k X) (d : ℤ) :
    coeff (-x) d = - coeff x d := rfl
@[simp] theorem coeff_sub (x y : LaurentModule k X) (d : ℤ) :
    coeff (x - y) d = coeff x d - coeff y d := rfl
@[simp] theorem coeff_smul (c : k) (x : LaurentModule k X) (d : ℤ) :
    coeff (c • x) d = c • coeff x d := rfl

/-- One lower bound applies to every nonzero coefficient vector. -/
def BoundedBelow (b : ℤ) (x : LaurentModule k X) : Prop :=
  ∀ d < b, coeff x d = 0

theorem exists_bound (x : LaurentModule k X) : ∃ b, BoundedBelow b x :=
  ⟨((HahnModule.of k).symm x).order, fun _ h ↦ HahnSeries.coeff_eq_zero_of_lt_order h⟩

/-- A constant vector, regarded as a Laurent series. -/
def single (d : ℤ) (x : X) : LaurentModule k X :=
  HahnModule.of k (HahnSeries.single d x)

@[simp] theorem coeff_single (d e : ℤ) (x : X) :
    coeff (single d x : LaurentModule k X) e = if e = d then x else 0 := by
  classical
  by_cases h : e = d <;> simp [coeff, single, h]

/-- Coefficientwise extension of a linear map. -/
def map (f : X →ₗ[k] Y) : LaurentModule k X →ₗ[LaurentSeries k] LaurentModule k Y where
  toFun x := HahnModule.of k (((HahnModule.of k).symm x).map f)
  map_add' x y := by
    ext d
    exact f.map_add _ _
  map_smul' a x := by
    apply HahnModule.ext
    funext d
    change f (((HahnModule.of k).symm (a • x)).coeff d) = _
    simp only [RingHom.id_apply]
    have hs : (((HahnModule.of k).symm x).map f).support ⊆
        ((HahnModule.of k).symm x).support := by
      intro n hn
      change f (((HahnModule.of k).symm x).coeff n) ≠ 0 at hn
      exact fun h ↦ hn (by rw [h, map_zero])
    rw [HahnModule.coeff_smul, map_sum]
    rw [HahnModule.coeff_smul_right (R := k) (x := a)
      (y := HahnModule.of k (((HahnModule.of k).symm x).map f))
      ((HahnModule.of k).symm x).isPWO_support hs]
    apply Finset.sum_congr rfl
    intro p hp
    exact f.map_smul _ _

@[simp] theorem coeff_map (f : X →ₗ[k] Y) (x : LaurentModule k X) (d : ℤ) :
    coeff (map f x) d = f (coeff x d) := rfl

@[simp] theorem map_id : map (LinearMap.id : X →ₗ[k] X) = LinearMap.id := by
  ext x d
  rfl

@[simp] theorem map_comp (g : Y →ₗ[k] Z) (f : X →ₗ[k] Y) :
    map (g.comp f) = (map g).comp (map f) := by
  ext x d
  rfl

@[simp] theorem map_single (f : X →ₗ[k] Y) (d : ℤ) (x : X) :
    map f (single d x) = single d (f x) := by
  ext e
  simp only [coeff_map, coeff_single]
  split <;> simp_all

theorem boundedBelow_map (f : X →ₗ[k] Y) {b : ℤ} {x : LaurentModule k X}
    (h : BoundedBelow b x) : BoundedBelow b (map f x) := by
  intro d hd
  simp [h d hd]

/-- Multiplying two lower-bounded series adds their lower bounds. -/
theorem boundedBelow_series_smul {a : LaurentSeries k} {x : LaurentModule k X}
    {b c : ℤ} (ha : ∀ d < b, a.coeff d = 0) (hx : BoundedBelow c x) :
    BoundedBelow (b + c) (a • x) := by
  intro d hd
  change ((HahnModule.of k).symm (a • x)).coeff d = 0
  rw [HahnModule.coeff_smul]
  apply Finset.sum_eq_zero
  intro p hp
  have hp' := (Finset.mem_vaddAntidiagonal _ _).mp hp
  have heq : p.1 + p.2 = d := hp'.2.2
  by_cases h : p.1 < b
  · rw [ha _ h, zero_smul]
  · have h' : p.2 < c := by omega
    change a.coeff p.1 • coeff x p.2 = 0
    rw [hx _ h', smul_zero]

@[simp] theorem coeff_series_single_smul (e : ℤ) (c : k) (x : LaurentModule k X) (d : ℤ) :
    coeff (HahnSeries.single e c • x) d = c • coeff x (d - e) := by
  have h := HahnModule.coeff_single_smul_vadd (R := k) (x := x)
    (r := c) (b := e) (a := d - e)
  simpa only [vadd_eq_add, add_sub_cancel, coeff] using h

/-- A Laurent series truncated above has an explicit finite monomial expansion. -/
theorem truncLT_eq_sum (a : LaurentSeries k) (B : ℤ) :
    HahnSeries.truncLT B a =
      ∑ e ∈ Finset.Ico a.order B, HahnSeries.single e (a.coeff e) := by
  classical
  ext d
  simp only [HahnSeries.coeff_truncLT, HahnSeries.coeff_sum]
  by_cases hd : d ∈ Finset.Ico a.order B
  · rw [Finset.sum_eq_single_of_mem d hd]
    · simp [(Finset.mem_Ico.mp hd).2]
    · intro e he hne
      simp [Ne.symm hne]
  · have hz : (∑ e ∈ Finset.Ico a.order B,
        (HahnSeries.single e (a.coeff e)).coeff d) = 0 := by
      apply Finset.sum_eq_zero
      intro e he
      have hne : d ≠ e := by intro h; subst e; exact hd he
      simp [hne]
    rw [hz]
    by_cases h : d < B
    · have hlow : d < a.order := by simpa [Finset.mem_Ico, h] using hd
      simp [h, HahnSeries.coeff_eq_zero_of_lt_order hlow]
    · simp [h]

theorem series_sub_truncLT_bound (a : LaurentSeries k) (B : ℤ) :
    ∀ d < B, (a - HahnSeries.truncLT B a).coeff d = 0 := by
  intro d hd
  simp [HahnSeries.coeff_sub, HahnSeries.coeff_truncLT, hd]

/-- A uniformly bounded coefficient-linear map commuting with scalar monomials
commutes with all Laurent scalars. Only finite truncations are used in the proof. -/
theorem map_series_smul_of_bounded (T : LaurentModule k X →ₗ[k] LaurentModule k Y)
    (C : ℤ)
    (hbound : ∀ b x, BoundedBelow b x → BoundedBelow (b + C) (T x))
    (hmonomial : ∀ (e : ℤ) (c : k) (x : LaurentModule k X),
      T (HahnSeries.single e c • x) = HahnSeries.single e c • T x)
    (a : LaurentSeries k) (x : LaurentModule k X) : T (a • x) = a • T x := by
  classical
  obtain ⟨b, hb⟩ := exists_bound x
  ext d
  let B : ℤ := d - b - C + 1
  let a₀ := HahnSeries.truncLT B a
  have hfinite : T (a₀ • x) = a₀ • T x := by
    dsimp only [a₀]
    rw [truncLT_eq_sum]
    simp only [Finset.sum_smul, map_sum, hmonomial]
  have htail := boundedBelow_series_smul (series_sub_truncLT_bound a B) hb
  have hleft := hbound (B + b) ((a - a₀) • x) htail d (by dsimp [B]; omega)
  have hright := boundedBelow_series_smul (series_sub_truncLT_bound a B)
    (hbound b x hb) d (by dsimp [B]; omega)
  change coeff (T ((a - a₀) • x)) d = 0 at hleft
  change coeff ((a - a₀) • T x) d = 0 at hright
  rw [sub_smul, map_sub, coeff_sub] at hleft
  rw [sub_smul, coeff_sub] at hright
  exact (sub_eq_zero.mp hleft).trans ((congrArg (fun y ↦ coeff y d) hfinite).trans
    (sub_eq_zero.mp hright).symm)

/-- A finite truncation of a vector-valued Laurent series. -/
def trunc (B : ℤ) (x : LaurentModule k X) : LaurentModule k X :=
  HahnModule.of k (HahnSeries.truncLT B ((HahnModule.of k).symm x))

@[simp] theorem coeff_trunc (B : ℤ) (x : LaurentModule k X) (d : ℤ) :
    coeff (trunc B x) d = if d < B then coeff x d else 0 := by
  classical
  by_cases h : d < B <;> simp [coeff, trunc, h]

theorem trunc_eq_sum (B : ℤ) (x : LaurentModule k X) :
    trunc B x = ∑ e ∈ Finset.Ico ((HahnModule.of k).symm x).order B, single e (coeff x e) := by
  classical
  ext d
  change coeff (trunc B x) d = ((HahnModule.of k).symm
    (∑ e ∈ Finset.Ico ((HahnModule.of k).symm x).order B, single e (coeff x e))).coeff d
  rw [coeff_trunc]
  change (if d < B then coeff x d else 0) =
    (∑ e ∈ Finset.Ico ((HahnModule.of k).symm x).order B,
      HahnSeries.single e (coeff x e)).coeff d
  rw [HahnSeries.coeff_sum]
  by_cases hd : d ∈ Finset.Ico ((HahnModule.of k).symm x).order B
  · rw [Finset.sum_eq_single_of_mem d hd]
    · simp [(Finset.mem_Ico.mp hd).2]
    · intro e he hne
      simp [Ne.symm hne]
  · have hz : (∑ e ∈ Finset.Ico ((HahnModule.of k).symm x).order B,
        (HahnSeries.single e (coeff x e)).coeff d) = 0 := by
      apply Finset.sum_eq_zero
      intro e he
      have hne : d ≠ e := by intro h; subst e; exact hd he
      simp [hne]
    rw [hz]
    by_cases h : d < B
    · have hlow : d < ((HahnModule.of k).symm x).order := by
        simpa [Finset.mem_Ico, h] using hd
      have hc : coeff x d = 0 := HahnSeries.coeff_eq_zero_of_lt_order hlow
      simp [h, hc]
    · simp [h]

theorem boundedBelow_sub_trunc (B : ℤ) (x : LaurentModule k X) :
    BoundedBelow B (x - trunc B x) := by
  intro d hd
  simp [hd]

theorem boundedBelow_single (e : ℤ) (x : X) : BoundedBelow e (single e x : LaurentModule k X) := by
  intro d hd
  simp [ne_of_lt hd]

/-- A uniformly bounded linear map is determined by its values on monomials. -/
theorem linear_eq_zero_of_bounded (T : LaurentModule k X →ₗ[k] LaurentModule k Y)
    (C : ℤ) (hbound : ∀ b x, BoundedBelow b x → BoundedBelow (b + C) (T x))
    (hsingle : ∀ e v, T (single e v) = 0) : T = 0 := by
  classical
  ext x d
  let B : ℤ := d - C + 1
  have hz : T (trunc B x) = 0 := by
    rw [trunc_eq_sum, map_sum]
    simp only [hsingle, Finset.sum_const_zero]
  have h := hbound B (x - trunc B x) (boundedBelow_sub_trunc B x) d (by dsimp [B]; omega)
  simpa only [map_sub, hz, sub_zero, LinearMap.zero_apply, coeff_zero] using h

theorem linear_ext_of_bounded (T S : LaurentModule k X →ₗ[k] LaurentModule k Y)
    (C : ℤ)
    (hT : ∀ b x, BoundedBelow b x → BoundedBelow (b + C) (T x))
    (hS : ∀ b x, BoundedBelow b x → BoundedBelow (b + C) (S x))
    (hsingle : ∀ e v, T (single e v) = S (single e v)) : T = S := by
  apply sub_eq_zero.mp
  apply linear_eq_zero_of_bounded (T - S) C
  · intro b x hx d hd
    change coeff (T x - S x) d = 0
    simp only [coeff_sub, hT b x hx d hd, hS b x hx d hd, sub_self]
  · intro e v
    exact sub_eq_zero.mpr (hsingle e v)

end LaurentModule
end EnvelopingIsomorphism.FormalSeries
