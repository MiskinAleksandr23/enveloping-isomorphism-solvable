import EnvelopingIsomorphism.Descent.FilteredCocycle
import EnvelopingIsomorphism.Descent.FiniteLog
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Algebra.Module.Rat
import Mathlib.Algebra.Algebra.Rat

/-!
The concrete linear layers for cocycles of filtered Lie automorphisms.
An action on Lie automorphisms and a compatible rational-linear action on
endomorphisms induce the quotient actions needed for finite averaging.
-/

namespace EnvelopingIsomorphism.Descent

universe u v w
variable {k : Type u} [Field k] [CharZero k]
variable {L : Type v} [LieRing L] [LieAlgebra k L] [LieAlgebra ℚ L]
variable {Γ : Type w} [Group Γ]

namespace FiniteFiltration

variable (F : FiniteFiltration k L)

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The additive quotient detecting the next filtration layer. -/
abbrev firstOrderSpace (r : ℕ) :=
  (Module.End k L) ⧸ (F.raisingSubmodule (r + 2)).restrictScalars ℚ

/-- Projection of an endomorphism to its first-order observation. -/
def firstOrderProjection (r : ℕ) : Module.End k L →ₗ[ℚ] F.firstOrderSpace r :=
  ((F.raisingSubmodule (r + 2)).restrictScalars ℚ).mkQ

/-- Observe the difference of a Lie automorphism from the identity. -/
def firstOrderObserve (r : ℕ) (u : L ≃ₗ⁅k⁆ L) : F.firstOrderSpace r :=
  F.firstOrderProjection r (u.toLinearMap - 1)

theorem firstOrderProjection_eq_iff (r : ℕ) (T S : Module.End k L) :
    F.firstOrderProjection r T = F.firstOrderProjection r S ↔
      T - S ∈ F.raisingSubmodule (r + 2) :=
  Submodule.Quotient.eq _

theorem firstOrderObserve_mul (r : ℕ) (u v : L ≃ₗ⁅k⁆ L)
    (hu : u ∈ F.automorphismSubgroup r) (hv : v ∈ F.automorphismSubgroup r) :
    F.firstOrderObserve r (u * v) = F.firstOrderObserve r u + F.firstOrderObserve r v := by
  unfold firstOrderObserve
  rw [← map_add, F.firstOrderProjection_eq_iff]
  exact F.mul_firstOrder (by omega) u v hu hv

theorem firstOrderObserve_eq_zero_iff (r : ℕ) (u : L ≃ₗ⁅k⁆ L) :
    F.firstOrderObserve r u = 0 ↔ u ∈ F.automorphismSubgroup (r + 1) := by
  change Submodule.Quotient.mk (u.toLinearMap - 1) = 0 ↔ _
  exact Submodule.Quotient.mk_eq_zero _

/-- Filtration-raising derivations, considered as a rational vector space. -/
abbrev correctionSpace (r : ℕ) := (F.raisingDerivations (r + 1)).restrictScalars ℚ

/-- The first-order part of a filtration-raising derivation. -/
def correctionLinearPart (r : ℕ) : F.correctionSpace r →ₗ[ℚ] F.firstOrderSpace r :=
  (F.firstOrderProjection r).comp
    (((LieDerivation.toLinearMapLieHom k L).toLinearMap.restrictScalars ℚ).comp
      ((F.raisingDerivations (r + 1)).restrictScalars ℚ).subtype)

@[simp] theorem correctionLinearPart_apply (r : ℕ) (D : F.correctionSpace r) :
    F.correctionLinearPart r D = F.firstOrderProjection r (D : LieDerivation k L L).toLinearMap :=
  rfl

/-- The exponential gives a genuine Lie automorphism correcting one layer. -/
noncomputable def correctionExponential (r : ℕ) (D : F.correctionSpace r) : L ≃ₗ⁅k⁆ L :=
  (D : LieDerivation k L L).exp (F.isNilpotent (by omega) D.property)

theorem correctionExponential_mem (r : ℕ) (D : F.correctionSpace r) :
    F.correctionExponential r D ∈ F.automorphismSubgroup r :=
  F.lieDerivation_exp_mem D D.property

theorem correctionExponential_observe (r : ℕ) (D : F.correctionSpace r) :
    F.firstOrderObserve r (F.correctionExponential r D) = F.correctionLinearPart r D := by
  rw [correctionLinearPart_apply]
  apply (F.firstOrderProjection_eq_iff r _ _).mpr
  exact F.lieDerivation_exp_firstOrder (by omega) D D.property

section Action

variable (ρ : Γ →* MulAut (L ≃ₗ⁅k⁆ L))
variable (α : Γ →* Module.End ℚ (Module.End k L))
variable (hstable : ∀ σ r T, T ∈ F.raisingSubmodule r → α σ T ∈ F.raisingSubmodule r)
variable (hcompatible : ∀ σ u,
  (ρ σ u).toLinearMap - 1 = α σ (u.toLinearMap - 1))

/-- The action induced on the quotient endomorphism space. -/
def firstOrderAction (r : ℕ) : Γ →* Module.End ℚ (F.firstOrderSpace r) where
  toFun σ := ((F.raisingSubmodule (r + 2)).restrictScalars ℚ).mapQ
    ((F.raisingSubmodule (r + 2)).restrictScalars ℚ) (α σ)
    (fun T hT => hstable σ (r + 2) T hT)
  map_one' := by
    ext T
    simp
  map_mul' σ τ := by
    ext T
    simp

@[simp] theorem firstOrderAction_projection (r : ℕ) (σ : Γ) (T : Module.End k L) :
    F.firstOrderAction α hstable r σ (F.firstOrderProjection r T) =
      F.firstOrderProjection r (α σ T) :=
  rfl

/-- The abstract first-order layer instantiated by actual Lie endomorphism quotients. -/
def lieFirstOrderLayer (r : ℕ) :
    FirstOrderLayer ρ (F.automorphismSubgroup r) (F.automorphismSubgroup (r + 1))
      (F.firstOrderAction α hstable r) where
  observe := F.firstOrderObserve r
  stable σ u hu := by
    change (ρ σ u).toLinearMap - 1 ∈ F.raisingSubmodule (r + 1)
    rw [hcompatible]
    exact hstable σ (r + 1) _ hu
  observe_mul u hu v hv := F.firstOrderObserve_mul r u v hu hv
  observe_action σ u _ := by
    simp only [firstOrderObserve, firstOrderAction_projection, hcompatible]
  mem_next u _ hu := (F.firstOrderObserve_eq_zero_iff r u).mp hu

omit [CharZero k] [LieAlgebra ℚ L] in
/-- The concrete automorphism filtration terminates. -/
theorem automorphismSubgroup_length_eq_bot : F.automorphismSubgroup F.length = ⊥ := by
  apply le_bot_iff.mp
  intro u hu
  exact F.automorphism_eq_one (by omega) hu

include α hstable hcompatible in
/-- Once logarithms have the proved first-order tangent property, every finite
cocycle of filtration-trivial Lie automorphisms is a coboundary.  All quotient,
exponential, and induction data are constructed here, rather than assumed. -/
theorem exists_lie_coboundary_of_logarithm [Fintype Γ]
    (logarithm : ∀ r, F.automorphismSubgroup r → F.correctionSpace r)
    (hlog : ∀ r (u : F.automorphismSubgroup r),
      (logarithm r u : LieDerivation k L L).toLinearMap -
        ((u : L ≃ₗ⁅k⁆ L).toLinearMap - 1) ∈ F.raisingSubmodule (r + 2))
    (a : Γ → (L ≃ₗ⁅k⁆ L)) (ha : IsGroupCocycle ρ a)
    (hmem : ∀ σ, a σ ∈ F.automorphismSubgroup 0) :
    ∃ b ∈ F.automorphismSubgroup 0, ∀ σ, a σ = b⁻¹ * ρ σ b := by
  classical
  let totalLog : ∀ r, (L ≃ₗ⁅k⁆ L) → F.correctionSpace r :=
    fun r u => if hu : u ∈ F.automorphismSubgroup r then logarithm r ⟨u, hu⟩ else 0
  apply exists_coboundary_of_linear_corrections ρ F.automorphismSubgroup F.length
    F.automorphismSubgroup_antitone F.automorphismSubgroup_length_eq_bot
    F.firstOrderSpace (fun r => F.correctionSpace r) (F.firstOrderAction α hstable)
    (F.lieFirstOrderLayer ρ α hstable hcompatible)
    F.correctionLinearPart totalLog F.correctionExponential ?_ ?_ ?_ a ha hmem
  · intro r _ u hu
    change F.correctionLinearPart r (totalLog r u) = F.firstOrderObserve r u
    simp only [totalLog, dif_pos hu, correctionLinearPart_apply, firstOrderObserve]
    exact (F.firstOrderProjection_eq_iff r _ _).mpr (hlog r ⟨u, hu⟩)
  · intro r _ d
    exact F.correctionExponential_mem r d
  · intro r _ d
    exact F.correctionExponential_observe r d

include α hstable hcompatible in
/-- Every finite-group cocycle of filtered Lie automorphisms inducing identity
on the associated graded is a coboundary.  The logarithms are the polynomial
tangent operators constructed in `FiniteLog`. -/
theorem exists_lie_coboundary [Fintype Γ]
    (a : Γ → (L ≃ₗ⁅k⁆ L)) (ha : IsGroupCocycle ρ a)
    (hmem : ∀ σ, a σ ∈ F.automorphismSubgroup 0) :
    ∃ b ∈ F.automorphismSubgroup 0, ∀ σ, a σ = b⁻¹ * ρ σ b := by
  apply F.exists_lie_coboundary_of_logarithm ρ α hstable hcompatible
    (fun r u => ⟨F.logDerivation (r := r + 1) (by omega) u u.property,
      F.logDerivation_mem (by omega) u u.property⟩) ?_ a ha hmem
  intro r u
  exact F.logDerivation_firstOrder (by omega) u u.property

end Action

end FiniteFiltration

end EnvelopingIsomorphism.Descent
