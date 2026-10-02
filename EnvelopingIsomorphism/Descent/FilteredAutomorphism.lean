import Mathlib.Algebra.Lie.Derivation.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing

/-! Finite filtrations and endomorphisms increasing their degree. -/

namespace EnvelopingIsomorphism.Descent

universe u v
variable (k : Type u) [Field k] (V : Type v) [AddCommGroup V] [Module k V]

/-- A decreasing filtration starting at the whole space and ending after finitely many steps. -/
structure FiniteFiltration where
  step : ℕ → Submodule k V
  length : ℕ
  step_zero : step 0 = ⊤
  antitone : Antitone step
  step_length : step length = ⊥

namespace FiniteFiltration

variable {k V} (F : FiniteFiltration k V)

theorem step_eq_bot {i : ℕ} (hi : F.length ≤ i) : F.step i = ⊥ := by
  apply le_bot_iff.mp
  simpa only [F.step_length] using F.antitone hi

/-- Operators increasing the filtration index by at least `r`. -/
def raisingSubmodule (r : ℕ) : Submodule k (Module.End k V) where
  carrier := {T | ∀ i x, x ∈ F.step i → T x ∈ F.step (i + r)}
  zero_mem' := by simp
  add_mem' := by
    intro T S hT hS i x hx
    exact (F.step (i + r)).add_mem (hT i x hx) (hS i x hx)
  smul_mem' := by
    intro a T hT i x hx
    exact (F.step (i + r)).smul_mem a (hT i x hx)

@[simp] theorem mem_raisingSubmodule {r : ℕ} {T : Module.End k V} :
    T ∈ F.raisingSubmodule r ↔ ∀ i x, x ∈ F.step i → T x ∈ F.step (i + r) :=
  Iff.rfl

theorem raising_antitone : Antitone F.raisingSubmodule := by
  intro r s hrs T hT i x hx
  exact F.antitone (Nat.add_le_add_left hrs i) (hT i x hx)

theorem one_mem : (1 : Module.End k V) ∈ F.raisingSubmodule 0 := by
  simp

theorem mul_mem {r s : ℕ} {T S : Module.End k V}
    (hT : T ∈ F.raisingSubmodule r) (hS : S ∈ F.raisingSubmodule s) :
    T * S ∈ F.raisingSubmodule (r + s) := by
  intro i x hx
  simpa only [Module.End.mul_apply, Nat.add_assoc, Nat.add_comm s r] using
    hT (i + s) (S x) (hS i x hx)

theorem pow_mem {r : ℕ} {T : Module.End k V}
    (hT : T ∈ F.raisingSubmodule r) (n : ℕ) :
    T ^ n ∈ F.raisingSubmodule (n * r) := by
  induction n with
  | zero => simpa using F.one_mem
  | succ n ih => simpa only [pow_succ, Nat.succ_mul] using F.mul_mem ih hT

theorem eq_zero_of_mem {r : ℕ} {T : Module.End k V}
    (hT : T ∈ F.raisingSubmodule r) (hr : F.length ≤ r) : T = 0 := by
  ext x
  have hx : x ∈ F.step 0 := by simp [F.step_zero]
  have h := hT 0 x hx
  simpa only [Nat.zero_add, F.step_eq_bot hr, Submodule.mem_bot, LinearMap.zero_apply] using h

theorem raisingSubmodule_eq_bot {r : ℕ} (hr : F.length ≤ r) :
    F.raisingSubmodule r = ⊥ := by
  apply le_bot_iff.mp
  intro T hT
  exact F.eq_zero_of_mem hT hr

theorem pow_length_eq_zero {r : ℕ} {T : Module.End k V}
    (hr : 1 ≤ r) (hT : T ∈ F.raisingSubmodule r) : T ^ F.length = 0 :=
  F.eq_zero_of_mem (F.pow_mem hT F.length) (Nat.le_mul_of_pos_right _ hr)

theorem isNilpotent {r : ℕ} {T : Module.End k V}
    (hr : 1 ≤ r) (hT : T ∈ F.raisingSubmodule r) : IsNilpotent T :=
  ⟨F.length, F.pow_length_eq_zero hr hT⟩

/-- Product errors are invisible in the next layer, starting at positive degree. -/
theorem mul_mem_succ {r : ℕ} {T S : Module.End k V}
    (hr : 1 ≤ r) (hT : T ∈ F.raisingSubmodule r) (hS : S ∈ F.raisingSubmodule r) :
    T * S ∈ F.raisingSubmodule (r + 1) :=
  F.raising_antitone (by omega) (F.mul_mem hT hS)

theorem pow_mem_succ {r n : ℕ} {T : Module.End k V}
    (hr : 1 ≤ r) (hn : 2 ≤ n) (hT : T ∈ F.raisingSubmodule r) :
    T ^ n ∈ F.raisingSubmodule (r + 1) := by
  apply F.raising_antitone (show r + 1 ≤ n * r by nlinarith)
  exact F.pow_mem hT n

end FiniteFiltration

section LieAutomorphisms

variable {k : Type u} [Field k] {L : Type v} [LieRing L] [LieAlgebra k L]

/-- Lie self-equivalences form a group, with multiplication given by composition. -/
instance lieEquivGroup : Group (L ≃ₗ⁅k⁆ L) where
  mul f g := g.trans f
  one := 1
  inv := LieEquiv.symm
  mul_assoc _ _ _ := by ext; rfl
  one_mul _ := by ext; rfl
  mul_one _ := by ext; rfl
  inv_mul_cancel f := by ext x; exact f.symm_apply_apply x

@[simp] theorem lieEquiv_mul_apply (f g : L ≃ₗ⁅k⁆ L) (x : L) : (f * g) x = f (g x) := rfl
@[simp] theorem lieEquiv_inv_apply (f : L ≃ₗ⁅k⁆ L) (x : L) : f⁻¹ x = f.symm x := rfl
@[simp] theorem lieEquiv_mul_toLinearMap (f g : L ≃ₗ⁅k⁆ L) :
    (f * g).toLinearMap = f.toLinearMap * g.toLinearMap := rfl
@[simp] theorem lieEquiv_one_toLinearMap : (1 : L ≃ₗ⁅k⁆ L).toLinearMap = 1 := rfl

@[simp] theorem lieEquiv_pow_toLinearMap (u : L ≃ₗ⁅k⁆ L) (n : ℕ) :
    (u ^ n).toLinearMap = u.toLinearMap ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [pow_succ, lieEquiv_mul_toLinearMap, ih]

namespace FiniteFiltration

variable (F : FiniteFiltration k L)

theorem inverse_preserves {r : ℕ} (hr : 1 ≤ r) (u : L ≃ₗ⁅k⁆ L)
    (hu : u.toLinearMap - 1 ∈ F.raisingSubmodule r)
    (i : ℕ) (x : L) (hx : x ∈ F.step i) : u.symm x ∈ F.step i := by
  have aux : ∀ j, j ≤ i → u.symm x ∈ F.step j := by
    intro j
    induction j with
    | zero => intro; simp [F.step_zero]
    | succ j ih =>
      intro hji
      have hdiff : x - u.symm x ∈ F.step (j + r) := by
        simpa using hu j (u.symm x) (ih (by omega))
      have hxj : x ∈ F.step (j + 1) := F.antitone hji hx
      have hdj : x - u.symm x ∈ F.step (j + 1) :=
        F.antitone (by omega) hdiff
      simpa using (F.step (j + 1)).sub_mem hxj hdj
  exact aux i le_rfl

theorem inverse_sub_one_mem {r : ℕ} (hr : 1 ≤ r) (u : L ≃ₗ⁅k⁆ L)
    (hu : u.toLinearMap - 1 ∈ F.raisingSubmodule r) :
    u.symm.toLinearMap - 1 ∈ F.raisingSubmodule r := by
  intro i x hx
  have hdiff : x - u.symm x ∈ F.step (i + r) := by
    simpa using hu i (u.symm x) (F.inverse_preserves hr u hu i x hx)
  simpa using (F.step (i + r)).neg_mem hdiff

theorem mul_sub_one_mem {r : ℕ} (u v : L ≃ₗ⁅k⁆ L)
    (hu : u.toLinearMap - 1 ∈ F.raisingSubmodule r)
    (hv : v.toLinearMap - 1 ∈ F.raisingSubmodule r) :
    (u * v).toLinearMap - 1 ∈ F.raisingSubmodule r := by
  have hm : (u.toLinearMap - 1) * (v.toLinearMap - 1) ∈ F.raisingSubmodule r :=
    F.raising_antitone (Nat.le_add_right r r) (F.mul_mem hu hv)
  have heq : (u * v).toLinearMap - 1 =
      (u.toLinearMap - 1) * (v.toLinearMap - 1) +
        (u.toLinearMap - 1) + (v.toLinearMap - 1) := by
    simp only [lieEquiv_mul_toLinearMap]
    noncomm_ring
  rw [heq]
  exact (F.raisingSubmodule r).add_mem ((F.raisingSubmodule r).add_mem hm hu) hv

/-- Automorphisms equal to the identity up to operators raising degree by `r+1`. -/
def automorphismSubgroup (r : ℕ) : Subgroup (L ≃ₗ⁅k⁆ L) where
  carrier := {u | u.toLinearMap - 1 ∈ F.raisingSubmodule (r + 1)}
  one_mem' := by simp
  mul_mem' := by intro u v hu hv; exact F.mul_sub_one_mem u v hu hv
  inv_mem' := by intro u hu; exact F.inverse_sub_one_mem (by omega) u hu

@[simp] theorem mem_automorphismSubgroup {r : ℕ} {u : L ≃ₗ⁅k⁆ L} :
    u ∈ F.automorphismSubgroup r ↔ u.toLinearMap - 1 ∈ F.raisingSubmodule (r + 1) := Iff.rfl

theorem automorphismSubgroup_antitone : Antitone F.automorphismSubgroup := by
  intro r s hrs u hu
  exact F.raising_antitone (Nat.add_le_add_right hrs 1) hu

theorem automorphism_eq_one {r : ℕ} (hr : F.length ≤ r + 1)
    {u : L ≃ₗ⁅k⁆ L} (hu : u ∈ F.automorphismSubgroup r) : u = 1 := by
  have h := F.eq_zero_of_mem hu hr
  have hu' : u.toLinearMap = 1 := sub_eq_zero.mp h
  ext x
  exact LinearMap.congr_fun hu' x

theorem mul_firstOrder {r : ℕ} (hr : 1 ≤ r) (u v : L ≃ₗ⁅k⁆ L)
    (hu : u.toLinearMap - 1 ∈ F.raisingSubmodule r)
    (hv : v.toLinearMap - 1 ∈ F.raisingSubmodule r) :
    ((u * v).toLinearMap - 1) - ((u.toLinearMap - 1) + (v.toLinearMap - 1)) ∈
      F.raisingSubmodule (r + 1) := by
  convert F.mul_mem_succ hr hu hv using 1 <;>
    simp only [lieEquiv_mul_toLinearMap] <;> noncomm_ring

end FiniteFiltration

end LieAutomorphisms

end EnvelopingIsomorphism.Descent
