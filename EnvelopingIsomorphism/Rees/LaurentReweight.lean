import EnvelopingIsomorphism.FormalSeries.Module
import EnvelopingIsomorphism.FormalSeries.Multilinear
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Uniform Laurent reweighting of operators on graded finite-support coordinates

An operator with uniformly bounded degree excess has a Laurent expansion in
endomorphisms after conjugation by degree scaling. The lower bound controls
the whole input space, while each individual input also gives an upper bound.
-/

noncomputable section

namespace EnvelopingIsomorphism.Rees

open Finsupp
open EnvelopingIsomorphism.FormalSeries

variable {k ι : Type*} [CommRing k]

/-- A uniform bound on output degree minus input degree. -/
def HasDegreeShift (w : ι → ℕ) (F : Module.End k (ι →₀ k)) (C : ℕ) : Prop :=
  ∀ i j, F (single i 1) j ≠ 0 → w j ≤ w i + C

/-- The degree-difference diagonal of an endomorphism. Every basis image is
filtered inside its existing finite support, then extended linearly. -/
def degreeDiagonal (w : ι → ℕ) (F : Module.End k (ι →₀ k)) (d : ℤ) :
    Module.End k (ι →₀ k) := by
  classical
  exact Finsupp.linearCombination k (fun i ↦
    (F (single i 1)).filter (fun j ↦ (w i : ℤ) - (w j : ℤ) = d))

@[simp] theorem degreeDiagonal_single (w : ι → ℕ) (F : Module.End k (ι →₀ k))
    (d : ℤ) (i : ι) (a : k) :
    degreeDiagonal w F d (single i a) =
      a • (F (single i 1)).filter (fun j ↦ (w i : ℤ) - (w j : ℤ) = d) := by
  classical
  simp [degreeDiagonal]

@[simp] theorem degreeDiagonal_single_one_apply (w : ι → ℕ)
    (F : Module.End k (ι →₀ k)) (d : ℤ) (i j : ι) :
    degreeDiagonal w F d (single i 1) j =
      if (w i : ℤ) - (w j : ℤ) = d then F (single i 1) j else 0 := by
  classical
  simp [Finsupp.filter_apply]

theorem degreeDiagonal_apply (w : ι → ℕ) (F : Module.End k (ι →₀ k))
    (d : ℤ) (x : ι →₀ k) (j : ι) :
    degreeDiagonal w F d x j =
      x.sum (fun i a ↦ a *
        if (w i : ℤ) - (w j : ℤ) = d then F (single i 1) j else 0) := by
  classical
  simp [degreeDiagonal, Finsupp.linearCombination_apply, Finsupp.sum,
    Finsupp.filter_apply]

/-- A single lower bound makes every diagonal below it the zero operator. -/
theorem degreeDiagonal_eq_zero_of_lt (w : ι → ℕ) (F : Module.End k (ι →₀ k))
    {C : ℕ} (hF : HasDegreeShift w F C) {d : ℤ} (hd : d < -(C : ℤ)) :
    degreeDiagonal w F d = 0 := by
  classical
  apply Finsupp.lhom_ext
  intro i a
  ext j
  simp only [degreeDiagonal_single, Finsupp.smul_apply, Finsupp.filter_apply,
    LinearMap.zero_apply, Finsupp.zero_apply]
  by_cases hij : (w i : ℤ) - (w j : ℤ) = d
  · rw [if_pos hij]
    have hz : F (single i 1) j = 0 := by
      by_contra hn
      have h := hF i j hn
      omega
    simp [hz]
  · simp [hij]

/-- The actual Laurent series of endomorphisms, with a common lower bound
valid simultaneously on all inputs. -/
def laurentReweight (w : ι → ℕ) (F : Module.End k (ι →₀ k))
    {C : ℕ} (hF : HasDegreeShift w F C) :
    LaurentModule k (Module.End k (ι →₀ k)) :=
  HahnModule.of k (HahnSeries.ofSuppBddBelow (degreeDiagonal w F) (by
    refine ⟨-(C : ℤ), ?_⟩
    intro d hd
    by_contra h
    exact hd (degreeDiagonal_eq_zero_of_lt w F hF (lt_of_not_ge h))))

@[simp] theorem coeff_laurentReweight (w : ι → ℕ) (F : Module.End k (ι →₀ k))
    {C : ℕ} (hF : HasDegreeShift w F C) (d : ℤ) :
    LaurentModule.coeff (laurentReweight w F hF) d = degreeDiagonal w F d := rfl

theorem boundedBelow_laurentReweight (w : ι → ℕ) (F : Module.End k (ι →₀ k))
    {C : ℕ} (hF : HasDegreeShift w F C) :
    LaurentModule.BoundedBelow (k := k) (X := Module.End k (ι →₀ k))
      (-(C : ℤ)) (laurentReweight w F hF) :=
  fun _ hd ↦ degreeDiagonal_eq_zero_of_lt w F hF hd

/-- Action of a Laurent endomorphism series on a constant input, coefficientwise. -/
def applyToConstant (T : LaurentModule k (Module.End k (ι →₀ k))) (x : ι →₀ k) :
    LaurentModule k (ι →₀ k) := LaurentModule.map (LinearMap.applyₗ x) T

@[simp] theorem coeff_applyToConstant
    (T : LaurentModule k (Module.End k (ι →₀ k))) (x : ι →₀ k) (d : ℤ) :
    LaurentModule.coeff (applyToConstant T x) d =
      LaurentModule.coeff (k := k) (X := Module.End k (ι →₀ k)) T d x := rfl

@[simp] theorem coeff_reweight_single (w : ι → ℕ) (F : Module.End k (ι →₀ k))
    {C : ℕ} (hF : HasDegreeShift w F C) (d : ℤ) (i j : ι) :
    LaurentModule.coeff (applyToConstant (laurentReweight w F hF) (single i 1)) d j =
      if (w i : ℤ) - (w j : ℤ) = d then F (single i 1) j else 0 :=
  degreeDiagonal_single_one_apply w F d i j

/-- A fixed input has no diagonal above its largest input degree. -/
theorem degreeDiagonal_apply_eq_zero_of_gt (w : ι → ℕ)
    (F : Module.End k (ι →₀ k)) (x : ι →₀ k) {n : ℕ}
    (hx : ∀ i ∈ x.support, w i ≤ n) {d : ℤ} (hd : (n : ℤ) < d) :
    degreeDiagonal w F d x = 0 := by
  classical
  ext j
  rw [degreeDiagonal_apply]
  apply Finset.sum_eq_zero
  intro i hi
  have hwi := hx i hi
  have hdiff : (w i : ℤ) - (w j : ℤ) ≠ d := by omega
  simp [hdiff]

/-- Every fixed polynomial input gives a finite Laurent polynomial, even when
the whole operator has infinitely many nonzero diagonals. -/
theorem reweight_action_support_subset (w : ι → ℕ) (F : Module.End k (ι →₀ k))
    {C : ℕ} (hF : HasDegreeShift w F C) (x : ι →₀ k) {n : ℕ}
    (hx : ∀ i ∈ x.support, w i ≤ n) :
    ((HahnModule.of k).symm (applyToConstant (laurentReweight w F hF) x)).support ⊆
      Set.Icc (-(C : ℤ)) (n : ℤ) := by
  intro d hd
  change degreeDiagonal w F d x ≠ 0 at hd
  constructor
  · by_contra h
    have hz := degreeDiagonal_eq_zero_of_lt w F hF (lt_of_not_ge h)
    exact hd (by rw [hz]; rfl)
  · by_contra h
    exact hd (degreeDiagonal_apply_eq_zero_of_gt w F x hx (lt_of_not_ge h))

theorem reweight_action_finite_support (w : ι → ℕ) (F : Module.End k (ι →₀ k))
    {C : ℕ} (hF : HasDegreeShift w F C) (x : ι →₀ k) :
    ((HahnModule.of k).symm (applyToConstant (laurentReweight w F hF) x)).support.Finite := by
  classical
  exact (Set.finite_Icc (-(C : ℤ)) ((x.support.sup w : ℕ) : ℤ)).subset
    (reweight_action_support_subset w F hF x (fun _ hi ↦ Finset.le_sup hi))

@[simp] theorem degreeDiagonal_one (w : ι → ℕ) (d : ℤ) :
    degreeDiagonal w (1 : Module.End k (ι →₀ k)) d =
      if d = 0 then 1 else 0 := by
  classical
  apply Finsupp.lhom_ext
  intro i a
  ext j
  by_cases hji : j = i
  · subst j
    by_cases hd : d = 0 <;> simp [hd, eq_comm]
  · by_cases hd : d = 0 <;> simp [Finsupp.filter_apply, hji, hd]

/-- Apply the E2 estimate separately at each outer parameter degree. -/
def reweightFamily (w : ι → ℕ) (F : ℕ → Module.End k (ι →₀ k)) (D : ℕ)
    (hF : ∀ r, HasDegreeShift w (F r) (r * (D - 1))) :
    ℕ → LaurentModule k (Module.End k (ι →₀ k)) :=
  fun r ↦ laurentReweight w (F r) (hF r)

@[simp] theorem coeff_reweightFamily (w : ι → ℕ) (F : ℕ → Module.End k (ι →₀ k))
    (D : ℕ) (hF : ∀ r, HasDegreeShift w (F r) (r * (D - 1))) (r : ℕ) (d : ℤ) :
    LaurentModule.coeff (reweightFamily w F D hF r) d = degreeDiagonal w (F r) d := rfl

/-- The E3 lower bound is uniform on the entire polynomial space, separately
at each fixed power of the outer parameter. -/
theorem boundedBelow_reweightFamily (w : ι → ℕ) (F : ℕ → Module.End k (ι →₀ k))
    (D : ℕ) (hF : ∀ r, HasDegreeShift w (F r) (r * (D - 1))) (r : ℕ) :
    LaurentModule.BoundedBelow (k := k) (X := Module.End k (ι →₀ k))
      (-((r * (D - 1) : ℕ) : ℤ)) (reweightFamily w F D hF r) :=
  boundedBelow_laurentReweight w (F r) (hF r)

/-- The same coefficient family as an actual element of End(V)((h))[[t]],
whose multiplication is formal composition of endomorphisms. -/
def reweightPowerSeries (w : ι → ℕ) (F : ℕ → Module.End k (ι →₀ k)) (D : ℕ)
    (hF : ∀ r, HasDegreeShift w (F r) (r * (D - 1))) :
    PowerSeries (LaurentSeries (Module.End k (ι →₀ k))) :=
  PowerSeries.mk (fun r ↦ (HahnModule.of k).symm (reweightFamily w F D hF r))

@[simp] theorem coeff_reweightPowerSeries (w : ι → ℕ)
    (F : ℕ → Module.End k (ι →₀ k)) (D : ℕ)
    (hF : ∀ r, HasDegreeShift w (F r) (r * (D - 1))) (r : ℕ) (d : ℤ) :
    (PowerSeries.coeff r (reweightPowerSeries w F D hF)).coeff d =
      degreeDiagonal w (F r) d := by
  rw [reweightPowerSeries, PowerSeries.coeff_mk]
  rfl

/-- Reweighting retains the identity specialization in the outer parameter. -/
theorem constantCoeff_reweightPowerSeries (w : ι → ℕ)
    (F : ℕ → Module.End k (ι →₀ k)) (D : ℕ)
    (hF : ∀ r, HasDegreeShift w (F r) (r * (D - 1))) (h₀ : F 0 = 1) :
    PowerSeries.constantCoeff (reweightPowerSeries w F D hF) = 1 := by
  ext d
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, coeff_reweightPowerSeries, h₀,
    degreeDiagonal_one]
  by_cases hd : d = 0 <;> simp [hd]

/-- Regard an ordinary endomorphism as a one-input cochain. -/
def endToCochain : Module.End k (ι →₀ k) ≃ₗ[k]
    LaurentModule.Cochain k (ι →₀ k) (ι →₀ k) 1 :=
  MultilinearMap.ofSubsingletonₗ k k (ι →₀ k) (ι →₀ k) (0 : Fin 1)

/-- F4 supplies the action of the completed operator on all Laurent inputs.
This is a map into Laurent-linear endomorphisms, not an identification with
the entire space of such endomorphisms. -/
def actLaurent : LaurentModule k (Module.End k (ι →₀ k)) →ₗ[LaurentSeries k]
    Module.End (LaurentSeries k) (LaurentModule k (ι →₀ k)) :=
  (MultilinearMap.ofSubsingletonₗ (LaurentSeries k) (LaurentSeries k)
    (LaurentModule k (ι →₀ k)) (LaurentModule k (ι →₀ k)) (0 : Fin 1)).symm.toLinearMap.comp
    ((LaurentModule.extendCochain 1).comp
      (LaurentModule.map (k := k) (X := Module.End k (ι →₀ k))
        (Y := LaurentModule.Cochain k (ι →₀ k) (ι →₀ k) 1) endToCochain.toLinearMap))

theorem coeff_actLaurent (T : LaurentModule k (Module.End k (ι →₀ k)))
    (x : LaurentModule k (ι →₀ k)) (d : ℤ) :
    LaurentModule.coeff (actLaurent T x) d =
      ∑ᶠ a : Fin 2 → ℤ, if ∑ i, a i = d then
        (LaurentModule.coeff (k := k) (X := Module.End k (ι →₀ k)) T (a 0))
          (LaurentModule.coeff x (a 1)) else 0 := rfl

@[simp] theorem actLaurent_constant (T : LaurentModule k (Module.End k (ι →₀ k)))
    (x : ι →₀ k) :
    actLaurent T (LaurentModule.single 0 x) = applyToConstant T x := by
  change LaurentModule.extendCochain 1
    (LaurentModule.map (k := k) (X := Module.End k (ι →₀ k))
      (Y := LaurentModule.Cochain k (ι →₀ k) (ι →₀ k) 1) endToCochain.toLinearMap T)
    (fun _ ↦ LaurentModule.single 0 x) = _
  rw [LaurentModule.extendCochain_constants]
  apply LaurentModule.ext
  intro d
  rfl

/-- The constructed action is faithful, without claiming that every
Laurent-linear endomorphism comes from a uniformly bounded series. -/
theorem actLaurent_injective : Function.Injective (actLaurent (k := k) (ι := ι)) := by
  intro T U h
  apply LaurentModule.ext (k := k) (X := Module.End k (ι →₀ k))
  intro d
  apply LinearMap.ext
  intro x
  have hx := congrArg (fun G : Module.End (LaurentSeries k) (LaurentModule k (ι →₀ k)) ↦
    LaurentModule.coeff (G (LaurentModule.single 0 x)) d) h
  simpa only [actLaurent_constant, coeff_applyToConstant] using hx

theorem boundedBelow_actLaurent (T : LaurentModule k (Module.End k (ι →₀ k)))
    (x : LaurentModule k (ι →₀ k)) {B b : ℤ}
    (hT : LaurentModule.BoundedBelow (k := k) (X := Module.End k (ι →₀ k)) B T)
    (hx : LaurentModule.BoundedBelow b x) :
    LaurentModule.BoundedBelow (B + b) (actLaurent T x) := by
  have hmap := LaurentModule.boundedBelow_map (k := k) (X := Module.End k (ι →₀ k))
    (Y := LaurentModule.Cochain k (ι →₀ k) (ι →₀ k) 1)
    (endToCochain (k := k) (ι := ι)).toLinearMap hT
  have h := LaurentModule.boundedBelow_extendCochain 1
    (LaurentModule.map (k := k) (X := Module.End k (ι →₀ k))
      (Y := LaurentModule.Cochain k (ι →₀ k) (ι →₀ k) 1) endToCochain.toLinearMap T)
    (fun _ ↦ x) hmap (fun _ ↦ hx)
  simpa [actLaurent, MultilinearMap.ofSubsingletonₗ, MultilinearMap.ofSubsingleton] using h

theorem boundedBelow_reweight_action (w : ι → ℕ) (F : Module.End k (ι →₀ k))
    {C : ℕ} (hF : HasDegreeShift w F C) (x : LaurentModule k (ι →₀ k)) {b : ℤ}
    (hx : LaurentModule.BoundedBelow b x) :
    LaurentModule.BoundedBelow (-(C : ℤ) + b) (actLaurent (laurentReweight w F hF) x) :=
  boundedBelow_actLaurent _ x (boundedBelow_laurentReweight w F hF) hx

end EnvelopingIsomorphism.Rees
