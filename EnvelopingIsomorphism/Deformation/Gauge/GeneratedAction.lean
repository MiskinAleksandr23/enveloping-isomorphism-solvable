import EnvelopingIsomorphism.Deformation.Gauge.ConjugationAction
import Mathlib.GroupTheory.FreeGroup.Basic

/-! Elementary coordinate changes generate a genuine group action. Equivariance
and product preservation for all finite words are consequences of the generator
identities, so the source producer need not construct a separate global group
of Poisson automorphisms. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Gauge

open EnvelopingIsomorphism.FormalSeries

section FreeAction

variable {Γ X : Type*}

/-- Labels remember the genuine positive order of an elementary correction. -/
structure ElementaryLabel (V : Type*) where
  order : ℕ
  positive : 0 < order
  direction : V

/-- Actual elementary state equivalences act through the free group they generate. -/
@[reducible] def generatedMulAction (moves : Γ → Equiv.Perm X) : MulAction (FreeGroup Γ) X :=
  MulAction.compHom X (FreeGroup.lift moves)

/-- Equivariance on elementary generators propagates to every finite word,
including inverse generators. -/
theorem generated_equivariance {G H Y : Type*} [Group G] [Group H]
    [MulAction G X] [MulAction H Y]
    (g : Γ → G) (h : Γ → H) (P : X → Y)
    (hgen : ∀ γ x, P (g γ • x) = h γ • P x) (s : FreeGroup Γ) (x : X) :
    P (FreeGroup.lift g s • x) = FreeGroup.lift h s • P x := by
  induction s using FreeGroup.induction_on generalizing x with
  | C1 => simp
  | of γ => simpa using hgen γ x
  | inv_of γ ih =>
    have he := ih ((g γ)⁻¹ • x)
    simp only [FreeGroup.lift_apply_of, smul_inv_smul] at he
    rw [map_inv, FreeGroup.lift_apply_of, map_inv, FreeGroup.lift_apply_of]
    exact (eq_inv_smul_iff.mpr he.symm)
  | mul s t ihs iht =>
    rw [map_mul, mul_smul, ihs, iht, map_mul, mul_smul]

end FreeAction

section LinearActions

variable {k V : Type*} [CommRing k] [AddCommGroup V] [Module k V]

/-- The actual conjugation representation on bilinear operations. -/
@[reducible] def conjugationMulAction : MulAction (V ≃ₗ[k] V) (Binary k V) where
  smul := conjugate
  one_smul := conjugate_refl
  mul_smul g h B := by ext a b; rfl

theorem generated_conjugation {Γ X : Type*}
    (moves : Γ → Equiv.Perm X) (operators : Γ → V ≃ₗ[k] V) (P : X → Binary k V)
    (hgen : ∀ γ x, conjugate (operators γ) (P x) = P (moves γ x))
    (s : FreeGroup Γ) (x : X) :
    conjugate (FreeGroup.lift operators s) (P x) = P (FreeGroup.lift moves s x) := by
  letI := conjugationMulAction (k := k) (V := V)
  exact (generated_equivariance moves operators P (fun γ x ↦ (hgen γ x).symm) s x).symm

/-- Every finite composition inherits actual intertwining from its generators. -/
theorem generated_intertwines {Γ X : Type*}
    (moves : Γ → Equiv.Perm X) (operators : Γ → V ≃ₗ[k] V) (P : X → Binary k V)
    (hgen : ∀ γ x a b, operators γ (P x a b) = P (moves γ x) (operators γ a) (operators γ b))
    (s : FreeGroup Γ) (x : X) (a b : V) :
    FreeGroup.lift operators s (P x a b) =
      P (FreeGroup.lift moves s x) (FreeGroup.lift operators s a) (FreeGroup.lift operators s b) :=
  (conjugate_eq_iff _ _ _).mp
    (generated_conjugation moves operators P (fun γ x ↦ (conjugate_eq_iff _ _ _).mpr (hgen γ x)) s x) a b

/-- Actual formal operator units act as linear equivalences over all scalar series. -/
def operatorUnitEquivHom : (PowerSeries (Module.End k V))ˣ →*
    (PowerSeriesModule k V ≃ₗ[PowerSeries k] PowerSeriesModule k V) where
  toFun := operatorUnitEquiv
  map_one' := operatorUnitEquiv_one
  map_mul' F G := operatorUnitEquiv_mul F G

end LinearActions

section MappedOperators

open EnvelopingIsomorphism.FormalSeries PowerSeriesModule

variable {k V R : Type*} [CommRing k] [AddCommGroup V] [Module k V] [Ring R]

/-- A coefficient-ring representation induces actual complete operator equivalences. -/
def gaugeRepresentation (ρ : R →+* Module.End k V) : GaugeUnit R →*
    (PowerSeriesModule k V ≃ₗ[PowerSeries k] PowerSeriesModule k V) :=
  operatorUnitEquivHom.comp
    ((Units.map (PowerSeries.map ρ).toMonoidHom).comp (Subgroup.subtype _))

@[simp] theorem gaugeRepresentation_apply (ρ : R →+* Module.End k V) (G : GaugeUnit R)
    (p : PowerSeriesModule k V) :
    gaugeRepresentation ρ G p = operator (PowerSeries.map ρ G.series) p := rfl

theorem gaugeRepresentation_lift {Γ : Type*} (ρ : R →+* Module.End k V)
    (units : Γ → GaugeUnit R) (s : FreeGroup Γ) :
    gaugeRepresentation ρ (FreeGroup.lift units s) =
      FreeGroup.lift (fun γ ↦ gaugeRepresentation ρ (units γ)) s := by
  have h : (gaugeRepresentation ρ).comp (FreeGroup.lift units) =
      FreeGroup.lift (fun γ ↦ gaugeRepresentation ρ (units γ)) := by
    apply FreeGroup.ext_hom
    intro γ
    simp
  exact DFunLike.congr_fun h s

/-- The concrete coefficient representation intertwines every generated word. -/
theorem generatedGauge_intertwines {Γ X : Type*}
    (ρ : R →+* Module.End k V) (units : Γ → GaugeUnit R) (moves : Γ → Equiv.Perm X)
    (P : X → Binary (PowerSeries k) (PowerSeriesModule k V))
    (hgen : ∀ γ x a b,
      operator (PowerSeries.map ρ (units γ).series) (P x a b) =
        P (moves γ x) (operator (PowerSeries.map ρ (units γ).series) a)
          (operator (PowerSeries.map ρ (units γ).series) b))
    (s : FreeGroup Γ) (x : X) (a b : PowerSeriesModule k V) :
    operator (PowerSeries.map ρ (FreeGroup.lift units s).series) (P x a b) =
      P (FreeGroup.lift moves s x)
        (operator (PowerSeries.map ρ (FreeGroup.lift units s).series) a)
        (operator (PowerSeries.map ρ (FreeGroup.lift units s).series) b) := by
  have h := generated_intertwines moves (fun γ ↦ gaugeRepresentation ρ (units γ)) P hgen s x a b
  simpa only [← gaugeRepresentation_lift, gaugeRepresentation_apply] using h

end MappedOperators

end EnvelopingIsomorphism.Deformation.Gauge
