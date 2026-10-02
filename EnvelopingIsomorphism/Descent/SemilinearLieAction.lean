import EnvelopingIsomorphism.Descent.FilteredLieCocycle

/-!
Semilinear Lie symmetries act on linear Lie automorphisms and endomorphisms by
conjugation.  The induced endomorphism action is rational-linear, as required
by finite cocycle averaging.
-/

namespace EnvelopingIsomorphism.Descent

universe u v w
variable {k : Type u} [Field k]
variable {L : Type v} [LieRing L] [LieAlgebra k L]

local instance (κ : k ≃+* k) : RingHomInvPair κ.toRingHom κ.symm.toRingHom :=
  RingHomInvPair.of_ringEquiv κ

section Single

variable {κ : k ≃+* k} (e : L ≃ₛₗ[κ.toRingHom] L)
variable (he : ∀ x y : L, e ⁅x, y⁆ = ⁅e x, e y⁆)

include he in
lemma semilinear_symm_map_lie (x y : L) : e.symm ⁅x, y⁆ = ⁅e.symm x, e.symm y⁆ := by
  apply e.injective
  simp only [LinearEquiv.apply_symm_apply, he]

/-- Conjugate a linear Lie automorphism by a semilinear Lie symmetry. -/
def semilinearConjugate (u : L ≃ₗ⁅k⁆ L) : L ≃ₗ⁅k⁆ L where
  __ := (e.symm.trans u.toLinearEquiv).trans e
  map_lie' := by
    intro x y
    change e (u (e.symm ⁅x, y⁆)) = ⁅e (u (e.symm x)), e (u (e.symm y))⁆
    rw [semilinear_symm_map_lie e he, LieEquiv.map_lie, he]

@[simp] theorem semilinearConjugate_apply (u : L ≃ₗ⁅k⁆ L) (x : L) :
    semilinearConjugate e he u x = e (u (e.symm x)) := rfl

@[simp] theorem semilinearConjugate_toLinearMap (u : L ≃ₗ⁅k⁆ L) :
    (semilinearConjugate e he u).toLinearMap = e.conjRingEquiv u.toLinearMap := rfl

/-- Conjugation is an automorphism of the group of linear Lie automorphisms. -/
def semilinearConjugation : MulAut (L ≃ₗ⁅k⁆ L) where
  toFun := semilinearConjugate e he
  invFun := semilinearConjugate e.symm (semilinear_symm_map_lie e he)
  left_inv u := by
    ext x
    change e.symm (e (u (e.symm (e x)))) = u x
    exact (e.symm_apply_apply _).trans (congrArg u (e.symm_apply_apply x))
  right_inv u := by
    ext x
    change e (e.symm (u (e (e.symm x)))) = u x
    exact (e.apply_symm_apply _).trans (congrArg u (e.apply_symm_apply x))
  map_mul' u v := by
    ext x
    simp only [semilinearConjugate_apply, lieEquiv_mul_apply, LinearEquiv.symm_apply_apply]

variable [LieAlgebra ℚ L]

/-- Endomorphism conjugation is rational-linear, even for a semilinear symmetry. -/
def semilinearEndConjugation : Module.End ℚ (Module.End k L) where
  toFun := e.conjRingEquiv
  map_add' := e.conjRingEquiv.map_add
  map_smul' r T := map_rat_smul e.conjRingEquiv r T

@[simp] theorem semilinearEndConjugation_apply (T : Module.End k L) (x : L) :
    semilinearEndConjugation e T x = e (T (e.symm x)) := rfl

end Single

/-- A group action by semilinear bijections preserving the Lie bracket. -/
structure SemilinearLieAction (Γ : Type w) [Group Γ] (k : Type u) [Field k]
    (L : Type v) [LieRing L] [LieAlgebra k L] where
  scalar : Γ → (k ≃+* k)
  equiv : ∀ σ, L ≃ₛₗ[(scalar σ).toRingHom] L
  map_lie : ∀ σ (x y : L), equiv σ ⁅x, y⁆ = ⁅equiv σ x, equiv σ y⁆
  one_apply : ∀ x : L, equiv 1 x = x
  mul_apply : ∀ σ τ (x : L), equiv (σ * τ) x = equiv σ (equiv τ x)

namespace SemilinearLieAction

variable {Γ : Type w} [Group Γ] (A : SemilinearLieAction Γ k L)

@[simp] theorem symm_one_apply (x : L) : (A.equiv 1).symm x = x := by
  calc
    (A.equiv 1).symm x = A.equiv 1 ((A.equiv 1).symm x) := (A.one_apply _).symm
    _ = x := (A.equiv 1).apply_symm_apply x

theorem symm_mul_apply (σ τ : Γ) (x : L) :
    (A.equiv (σ * τ)).symm x = (A.equiv τ).symm ((A.equiv σ).symm x) := by
  apply (A.equiv (σ * τ)).injective
  rw [(A.equiv (σ * τ)).apply_symm_apply, A.mul_apply,
    (A.equiv τ).apply_symm_apply, (A.equiv σ).apply_symm_apply]

/-- The natural action on the group of linear Lie automorphisms. -/
def automorphismAction : Γ →* MulAut (L ≃ₗ⁅k⁆ L) where
  toFun σ := semilinearConjugation (A.equiv σ) (A.map_lie σ)
  map_one' := by
    ext u x
    change A.equiv 1 (u ((A.equiv 1).symm x)) = u x
    rw [A.one_apply, A.symm_one_apply]
  map_mul' σ τ := by
    ext u x
    change A.equiv (σ * τ) (u ((A.equiv (σ * τ)).symm x)) =
      A.equiv σ (A.equiv τ (u ((A.equiv τ).symm ((A.equiv σ).symm x))))
    rw [A.mul_apply, A.symm_mul_apply]

variable [LieAlgebra ℚ L]

/-- The natural rational-linear action on the endomorphism space. -/
def endomorphismAction : Γ →* Module.End ℚ (Module.End k L) where
  toFun σ := semilinearEndConjugation (A.equiv σ)
  map_one' := by
    ext T x
    change A.equiv 1 (T ((A.equiv 1).symm x)) = T x
    rw [A.one_apply, A.symm_one_apply]
  map_mul' σ τ := by
    ext T x
    change A.equiv (σ * τ) (T ((A.equiv (σ * τ)).symm x)) =
      A.equiv σ (A.equiv τ (T ((A.equiv τ).symm ((A.equiv σ).symm x))))
    rw [A.mul_apply, A.symm_mul_apply]

omit [LieAlgebra ℚ L] in
@[simp] theorem automorphismAction_apply (σ : Γ) (u : L ≃ₗ⁅k⁆ L) (x : L) :
    A.automorphismAction σ u x = A.equiv σ (u ((A.equiv σ).symm x)) := rfl

@[simp] theorem endomorphismAction_apply (σ : Γ) (T : Module.End k L) (x : L) :
    A.endomorphismAction σ T x = A.equiv σ (T ((A.equiv σ).symm x)) := rfl

/-- Conjugation commutes with taking the difference from the identity. -/
theorem action_compatible (σ : Γ) (u : L ≃ₗ⁅k⁆ L) :
    (A.automorphismAction σ u).toLinearMap - 1 =
      A.endomorphismAction σ (u.toLinearMap - 1) := by
  change (A.equiv σ).conjRingEquiv u.toLinearMap - 1 =
    (A.equiv σ).conjRingEquiv (u.toLinearMap - 1)
  rw [map_sub, map_one]

omit [LieAlgebra ℚ L] in
/-- The inverse of a symmetry is the symmetry indexed by the inverse group element. -/
theorem symm_apply_eq_inv (σ : Γ) (x : L) :
    (A.equiv σ).symm x = A.equiv σ⁻¹ x := by
  apply (A.equiv σ).injective
  rw [(A.equiv σ).apply_symm_apply, ← A.mul_apply, mul_inv_cancel, A.one_apply]

/-- An invariant vector-space filtration induces an invariant raising-operator filtration. -/
theorem endomorphismAction_stable (F : FiniteFiltration k L)
    (hF : ∀ σ i x, x ∈ F.step i → A.equiv σ x ∈ F.step i)
    (σ : Γ) (r : ℕ) (T : Module.End k L) (hT : T ∈ F.raisingSubmodule r) :
    A.endomorphismAction σ T ∈ F.raisingSubmodule r := by
  intro i x hx
  change A.equiv σ (T ((A.equiv σ).symm x)) ∈ F.step (i + r)
  apply hF σ (i + r)
  apply hT i
  rw [A.symm_apply_eq_inv]
  exact hF σ⁻¹ i x hx

/-- Triviality of cocycles of filtered Lie automorphisms for an actual semilinear
Lie action.  Both conjugation actions and all first-order exp/log data are
constructed, so only invariance of the underlying finite filtration is required. -/
theorem exists_coboundary [CharZero k] [Fintype Γ]
    (F : FiniteFiltration k L)
    (hF : ∀ σ i x, x ∈ F.step i → A.equiv σ x ∈ F.step i)
    (a : Γ → (L ≃ₗ⁅k⁆ L)) (ha : IsGroupCocycle A.automorphismAction a)
    (hmem : ∀ σ, a σ ∈ F.automorphismSubgroup 0) :
    ∃ b ∈ F.automorphismSubgroup 0,
      ∀ σ, a σ = b⁻¹ * A.automorphismAction σ b :=
  F.exists_lie_coboundary A.automorphismAction A.endomorphismAction
    (A.endomorphismAction_stable F hF) A.action_compatible a ha hmem

end SemilinearLieAction

end EnvelopingIsomorphism.Descent
