import EnvelopingIsomorphism.Deformation.Gauge.BoundaryStabilizer
import EnvelopingIsomorphism.Deformation.Gauge.ConjugationAction

/-! The actual action of near-identity operator units on complete associative
families with a fixed constant product. This is a concrete producer of the
target action, its leading term, and its degree minus one stabilizers. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Gauge

open EnvelopingIsomorphism.FormalSeries PowerSeriesModule

variable {k V : Type*} [CommRing k] [AddCommGroup V] [Module k V]

/-- Actual formal associative products with prescribed reduction modulo t. -/
def AssociativeSeries (μ : Binary k V) :=
  {B : PowerSeriesModule k (Binary k V) // coeffV 0 B = μ ∧
    ∀ x y z, extendBinary B (extendBinary B x y) z =
      extendBinary B x (extendBinary B y z)}

namespace AssociativeSeries

variable {μ : Binary k V}

@[ext] theorem ext {B C : AssociativeSeries μ} (h : B.val = C.val) : B = C :=
  Subtype.ext h

/-- This action is conjugation by the actual invertible operator on vector series. -/
def transport (G : GaugeUnit (Module.End k V)) (B : AssociativeSeries μ) :
    AssociativeSeries μ :=
  ⟨conjugateBinarySeries G.val B.val,
    (conjugateBinarySeries_agree G.val B.val G.near_one 0 (by decide)).trans B.property.1,
    by
      have h := conjugate_associative (operatorUnitEquiv G.val) (extendBinary B.val) B.property.2
      intro x y z
      simpa only [extendBinary_conjugateBinarySeries] using h x y z⟩

@[simp] theorem transport_val (G : GaugeUnit (Module.End k V)) (B : AssociativeSeries μ) :
    (transport G B).val = conjugateBinarySeries G.val B.val := rfl

@[simp] theorem transport_one (B : AssociativeSeries μ) : transport 1 B = B :=
  Subtype.ext (conjugateBinarySeries_one B.val)

theorem transport_mul (G H : GaugeUnit (Module.End k V)) (B : AssociativeSeries μ) :
    transport (G * H) B = transport G (transport H B) :=
  Subtype.ext (conjugateBinarySeries_mul G.val H.val B.val)

instance : MulAction (GaugeUnit (Module.End k V)) (AssociativeSeries μ) where
  smul := transport
  one_smul := transport_one
  mul_smul := transport_mul

@[simp] theorem smul_eq_transport (G : GaugeUnit (Module.End k V)) (B : AssociativeSeries μ) :
    G • B = transport G B := rfl

theorem transport_intertwines (G : GaugeUnit (Module.End k V)) (B : AssociativeSeries μ)
    (x y : PowerSeriesModule k V) :
    operatorUnitEquiv G.val (extendBinary B.val x y) =
      extendBinary (transport G B).val (operatorUnitEquiv G.val x) (operatorUnitEquiv G.val y) := by
  rw [transport_val, extendBinary_conjugateBinarySeries, conjugate_apply]
  simp only [LinearEquiv.symm_apply_apply]

theorem transport_agree (G : GaugeUnit (Module.End k V)) (B : AssociativeSeries μ)
    {N : ℕ} (hG : NearIdentity N G.series) : AgreeBelow N (transport G B).val B.val :=
  conjugateBinarySeries_agree G.val B.val hG

/-- The leading tangent is the negative Hochschild differential in degree zero. -/
theorem transport_leading (G : GaugeUnit (Module.End k V)) (B : AssociativeSeries μ)
    {N : ℕ} (hN : 0 < N) (hG : NearIdentity N G.series) :
    coeffV N (transport G B).val - coeffV N B.val =
      -differentialOne μ (PowerSeries.coeff N G.series) := by
  rw [transport_val, conjugateBinarySeries_leading_sub G.val B.val hN hG, B.property.1]
  rfl

end AssociativeSeries

section Stabilizer

variable {A : Type*} [CommRing A] [Algebra k A] [Algebra ℚ k] [Algebra ℚ A]
variable {μ : Binary k A}

/-- Every actual Hochschild boundary integrates to a stabilizer of the full family. -/
def AssociativeSeries.boundary (N : ℕ) (hN : 0 < N) (u : A) (B : AssociativeSeries μ) :
    GaugeUnit (Module.End k A) := boundaryGauge N hN B.val u

theorem AssociativeSeries.boundary_near (N : ℕ) (hN : 0 < N) (u : A)
    (B : AssociativeSeries μ) : NearIdentity N (B.boundary N hN u).series :=
  boundaryGauge_near N hN B.val u

theorem AssociativeSeries.boundary_leading (N : ℕ) (hN : 0 < N) (u : A)
    (B : AssociativeSeries μ) :
    PowerSeries.coeff N (B.boundary N hN u).series = differentialZero μ u := by
  rw [AssociativeSeries.boundary, boundaryGauge_leading, B.property.1]

theorem AssociativeSeries.boundary_fixes (N : ℕ) (hN : 0 < N) (u : A)
    (B : AssociativeSeries μ) : B.transport (B.boundary N hN u) = B := by
  apply AssociativeSeries.ext
  exact boundaryGauge_fixes N hN B.val u B.property.2

end Stabilizer

end EnvelopingIsomorphism.Deformation.Gauge
