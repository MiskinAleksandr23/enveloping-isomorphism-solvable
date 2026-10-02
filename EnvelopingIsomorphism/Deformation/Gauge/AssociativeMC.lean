import EnvelopingIsomorphism.Deformation.Gauge.AssociativeAction
import EnvelopingIsomorphism.FormalSeries.BinaryAssociator

/-! Concrete equivalence between complete coefficient Maurer-Cartan elements
and actual associative formal products. -/

noncomputable section

set_option maxSynthPendingDepth 3

namespace EnvelopingIsomorphism.Deformation.Gauge

open EnvelopingIsomorphism.FormalSeries PowerSeriesModule

variable {k V : Type*} [CommRing k] [AddCommGroup V] [Module k V]

abbrev AssociativeMC (μ : Binary k V) :=
  MCSeries (differentialTwoLinear μ) (insertBinaryLinear (k := k) (V := V))

/-- The MC element is exactly the positive part of the full product. -/
def mcEquivAssociative (μ : Binary k V)
    (hμ : ∀ a b c, μ (μ a b) c = μ a (μ b c)) :
    AssociativeMC μ ≃ AssociativeSeries μ where
  toFun b := ⟨single 0 μ + b.val,
    by simp [b.property.1],
    (quadratic_MC_iff_associative μ hμ b.val).mp b.property.2⟩
  invFun B := ⟨B.val - single 0 μ,
    by simp [B.property.1],
    by
      apply (quadratic_MC_iff_associative μ hμ _).mpr
      have h : single 0 μ + (B.val - single 0 μ) = B.val := by abel
      rw [h]
      exact B.property.2⟩
  left_inv b := Subtype.ext (by dsimp; abel)
  right_inv B := Subtype.ext (by dsimp; abel)

@[simp] theorem mcEquivAssociative_val (μ : Binary k V)
    (hμ : ∀ a b c, μ (μ a b) c = μ a (μ b c)) (b : AssociativeMC μ) :
    (mcEquivAssociative μ hμ b).val = single 0 μ + b.val := rfl

@[simp] theorem mcEquivAssociative_symm_val (μ : Binary k V)
    (hμ : ∀ a b c, μ (μ a b) c = μ a (μ b c)) (B : AssociativeSeries μ) :
    ((mcEquivAssociative μ hμ).symm B).val = B.val - single 0 μ := rfl

/-- Actual operator conjugation, expressed in coefficient MC coordinates. -/
def associativeMCTransport (μ : Binary k V)
    (hμ : ∀ a b c, μ (μ a b) c = μ a (μ b c))
    (G : GaugeUnit (Module.End k V)) (b : AssociativeMC μ) : AssociativeMC μ :=
  (mcEquivAssociative μ hμ).symm ((mcEquivAssociative μ hμ b).transport G)

@[simp] theorem associativeMCTransport_val (μ : Binary k V)
    (hμ : ∀ a b c, μ (μ a b) c = μ a (μ b c))
    (G : GaugeUnit (Module.End k V)) (b : AssociativeMC μ) :
    (associativeMCTransport μ hμ G b).val =
      conjugateBinarySeries G.val (single 0 μ + b.val) - single 0 μ := rfl

@[simp] theorem associativeMCTransport_one (μ : Binary k V)
    (hμ : ∀ a b c, μ (μ a b) c = μ a (μ b c)) (b : AssociativeMC μ) :
    associativeMCTransport μ hμ 1 b = b := by
  rw [associativeMCTransport, AssociativeSeries.transport_one, Equiv.symm_apply_apply]

theorem associativeMCTransport_mul (μ : Binary k V)
    (hμ : ∀ a b c, μ (μ a b) c = μ a (μ b c))
    (G H : GaugeUnit (Module.End k V)) (b : AssociativeMC μ) :
    associativeMCTransport μ hμ (G * H) b =
      associativeMCTransport μ hμ G (associativeMCTransport μ hμ H b) := by
  simp only [associativeMCTransport, AssociativeSeries.transport_mul, Equiv.apply_symm_apply]

/-- A genuine group action, derived from operator conjugation. -/
@[reducible] def associativeMCMulAction (μ : Binary k V)
    (hμ : ∀ a b c, μ (μ a b) c = μ a (μ b c)) :
    MulAction (GaugeUnit (Module.End k V)) (AssociativeMC μ) where
  smul := associativeMCTransport μ hμ
  one_smul := associativeMCTransport_one μ hμ
  mul_smul := associativeMCTransport_mul μ hμ

theorem associativeMCTransport_agree (μ : Binary k V)
    (hμ : ∀ a b c, μ (μ a b) c = μ a (μ b c))
    (G : GaugeUnit (Module.End k V)) (b : AssociativeMC μ)
    {N : ℕ} (hG : NearIdentity N G.series) :
    AgreeBelow N (associativeMCTransport μ hμ G b).val b.val := by
  intro i hi
  rw [associativeMCTransport_val, coeffV_sub,
    conjugateBinarySeries_agree G.val _ hG i hi, coeffV_add]
  abel

/-- The exact leading action demanded by elementary gauge reflection. -/
theorem associativeMCTransport_leading (μ : Binary k V)
    (hμ : ∀ a b c, μ (μ a b) c = μ a (μ b c))
    (G : GaugeUnit (Module.End k V)) (b : AssociativeMC μ)
    {N : ℕ} (hN : 0 < N) (hG : NearIdentity N G.series) :
    coeffV N (associativeMCTransport μ hμ G b).val - coeffV N b.val =
      -differentialOne μ (PowerSeries.coeff N G.series) := by
  have h := (mcEquivAssociative μ hμ b).transport_leading G hN hG
  rw [mcEquivAssociative_val, coeffV_add] at h
  rw [associativeMCTransport_val, coeffV_sub]
  change coeffV N ((mcEquivAssociative μ hμ b).transport G).val -
    coeffV N (single 0 μ) - coeffV N b.val = _
  rw [sub_sub]
  exact h

section Stabilizer

variable {A : Type*} [CommRing A] [Algebra k A] [Algebra ℚ k] [Algebra ℚ A]

def associativeMCBoundary (μ : Binary k A)
    (hμ : ∀ a b c, μ (μ a b) c = μ a (μ b c))
    (N : ℕ) (hN : 0 < N) (u : A) (b : AssociativeMC μ) : GaugeUnit (Module.End k A) :=
  (mcEquivAssociative μ hμ b).boundary N hN u

theorem associativeMCBoundary_near (μ : Binary k A)
    (hμ : ∀ a b c, μ (μ a b) c = μ a (μ b c))
    (N : ℕ) (hN : 0 < N) (u : A) (b : AssociativeMC μ) :
    NearIdentity N (associativeMCBoundary μ hμ N hN u b).series :=
  (mcEquivAssociative μ hμ b).boundary_near N hN u

theorem associativeMCBoundary_leading (μ : Binary k A)
    (hμ : ∀ a b c, μ (μ a b) c = μ a (μ b c))
    (N : ℕ) (hN : 0 < N) (u : A) (b : AssociativeMC μ) :
    PowerSeries.coeff N (associativeMCBoundary μ hμ N hN u b).series = differentialZero μ u :=
  (mcEquivAssociative μ hμ b).boundary_leading N hN u

theorem associativeMCBoundary_fixes (μ : Binary k A)
    (hμ : ∀ a b c, μ (μ a b) c = μ a (μ b c))
    (N : ℕ) (hN : 0 < N) (u : A) (b : AssociativeMC μ) :
    associativeMCTransport μ hμ (associativeMCBoundary μ hμ N hN u b) b = b := by
  change (mcEquivAssociative μ hμ).symm
    ((mcEquivAssociative μ hμ b).transport ((mcEquivAssociative μ hμ b).boundary N hN u)) = _
  rw [AssociativeSeries.boundary_fixes, Equiv.symm_apply_apply]

end Stabilizer

end EnvelopingIsomorphism.Deformation.Gauge
