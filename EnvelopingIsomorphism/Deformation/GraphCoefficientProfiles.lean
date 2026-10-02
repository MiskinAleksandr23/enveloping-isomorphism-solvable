import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Module.BigOperators

/-! Finite scalar coefficient profiles and explicit signed averaging.
The coefficients contain no cochains or operator identities. Evaluation is a
separate linear map, so a scalar relation can later be checked geometrically.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.GraphCoefficientProfiles

open scoped BigOperators Classical

section Ring

variable {k α ι V : Type*} [CommRing k] [Fintype α] [Fintype ι]
  [AddCommGroup V] [Module k V]

/-- Evaluate a scalar coefficient table on an arbitrary family of vectors. -/
def evaluation (F : α → V) : (α → k) →ₗ[k] V where
  toFun c := ∑ a, c a • F a
  map_add' c d := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' r c := by simp [Finset.smul_sum, smul_smul]

@[simp] theorem evaluation_apply (F : α → V) (c : α → k) :
    evaluation F c = ∑ a, c a • F a := rfl

/-- Push a finite weighted family onto its resulting graph labels. Every
assignment contributing to the same label is retained with its multiplicity. -/
def pushforward (f : ι → α) (w : ι → k) : α → k :=
  fun a ↦ ∑ i, if f i = a then w i else 0

omit [Fintype α] in
@[simp] theorem pushforward_apply (f : ι → α) (w : ι → k) (a : α) :
    pushforward f w a = ∑ i, if f i = a then w i else 0 := rfl

/-- The scalar fibre sum evaluates to exactly the original indexed operator sum. -/
theorem evaluation_pushforward (F : α → V) (f : ι → α) (w : ι → k) :
    evaluation F (pushforward f w) = ∑ i, w i • F (f i) := by
  classical
  simp only [evaluation_apply, pushforward_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  simp

/-- A signed relabelling acts on scalar coefficient tables by exact inverse image. -/
def signedTransport (σ : Equiv.Perm α) (ε : k) (c : α → k) : α → k :=
  fun a ↦ ε * c (σ.symm a)

theorem evaluation_signedTransport (F : α → V) (σ : Equiv.Perm α) (ε : k)
    (hε : ε * ε = 1) (hF : ∀ a, F (σ a) = ε • F a) (c : α → k) :
    evaluation F (signedTransport σ ε c) = evaluation F c := by
  classical
  change (∑ a, (ε * c (σ.symm a)) • F a) = ∑ a, c a • F a
  apply Fintype.sum_equiv σ.symm
  intro a
  have h := hF (σ.symm a)
  rw [Equiv.apply_symm_apply] at h
  rw [h, smul_smul]
  have he : ε * c (σ.symm a) * ε = c (σ.symm a) := by
    calc
      ε * c (σ.symm a) * ε = (ε * ε) * c (σ.symm a) := by ring
      _ = c (σ.symm a) := by rw [hε, one_mul]
  rw [he]

end Ring

section Average

variable {k α ι V G : Type*} [Field k] [CharZero k]
  [Fintype α] [Fintype ι] [Fintype G] [Nonempty G] [AddCommGroup V] [Module k V]

/-- Explicit finite signed averaging; no invariance of geometric weights is assumed. -/
def signedAverage (σ : G → Equiv.Perm α) (ε : G → k) (c : α → k) : α → k :=
  (Fintype.card G : k)⁻¹ • ∑ g, signedTransport (σ g) (ε g) c

theorem evaluation_signedAverage (F : α → V) (σ : G → Equiv.Perm α) (ε : G → k)
    (hε : ∀ g, ε g * ε g = 1) (hF : ∀ g a, F (σ g a) = ε g • F a)
    (c : α → k) : evaluation F (signedAverage σ ε c) = evaluation F c := by
  classical
  rw [signedAverage, map_smul, map_sum]
  simp only [evaluation_signedTransport F _ _ (hε _) (hF _), Finset.sum_const,
    Finset.card_univ, ← Nat.cast_smul_eq_nsmul k, smul_smul]
  rw [inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero), one_smul]

/-- A genuine scalar relation after signed relabelling suffices for the
corresponding operator relation, without requiring unsymmetrized coefficients to agree. -/
theorem evaluation_eq_of_signedAverage_eq (F : α → V)
    (σ : G → Equiv.Perm α) (ε : G → k)
    (hε : ∀ g, ε g * ε g = 1) (hF : ∀ g a, F (σ g a) = ε g • F a)
    {c d : α → k} (h : signedAverage σ ε c = signedAverage σ ε d) :
    evaluation F c = evaluation F d := by
  rw [← evaluation_signedAverage F σ ε hε hF c,
    ← evaluation_signedAverage F σ ε hε hF d, h]

omit [CharZero k] [Fintype α] [Nonempty G] in
/-- The averaged coefficient is a literal finite scalar sum over relabellings
and assignments producing the specified labelled graph. -/
theorem signedAverage_pushforward_apply (σ : G → Equiv.Perm α) (ε : G → k)
    (f : ι → α) (w : ι → k) (a : α) :
    signedAverage σ ε (pushforward f w) a =
      (Fintype.card G : k)⁻¹ * ∑ g, ε g * ∑ i, if σ g (f i) = a then w i else 0 := by
  classical
  simp only [signedAverage, Pi.smul_apply, Finset.sum_apply, signedTransport,
    smul_eq_mul, pushforward_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro g hg
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [(σ g).eq_symm_apply]

end Average

end EnvelopingIsomorphism.Deformation.GraphCoefficientProfiles
