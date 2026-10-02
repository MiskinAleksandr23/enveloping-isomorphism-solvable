import EnvelopingIsomorphism.Deformation.Kontsevich.GraphCoordinateDomain
import EnvelopingIsomorphism.Deformation.Kontsevich.WeightNormalization
import EnvelopingIsomorphism.Deformation.Kontsevich.GraphEdgeOrder
import EnvelopingIsomorphism.Deformation.GeneralGraphOperators
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Genuine geometric weights in normalized real coordinates

The domain is the proved open coordinate model of the actual normalized
configuration space. Edge order is explicit; no arbitrary finite enumeration
silently chooses an orientation. Defining an integral does not assert its
absolute convergence or a Stokes identity.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.GeometricWeights

open MeasureTheory
open scoped BigOperators

/-- The actual configuration domain in the displayed standard real-coordinate basis. -/
def realDomain (n m : ℕ) : Set (Fin (GraphForms.dimension n m) → ℝ) :=
  (GraphForms.realCoordinates n m).symm ⁻¹' GraphForms.admissibleSet n m

theorem isOpen_realDomain (n m : ℕ) : IsOpen (realDomain n m) :=
  (GraphForms.isOpen_admissibleSet n m).preimage
    (GraphForms.realCoordinates n m).symm.toContinuousLinearEquiv.continuous

theorem measurableSet_realDomain (n m : ℕ) : MeasurableSet (realDomain n m) :=
  (isOpen_realDomain n m).measurableSet

variable {n m : ℕ}

/-- Top-form coefficient in the same real coordinates used for Lebesgue integration. -/
def realDensity (edges : Fin (GraphForms.dimension n m) → GraphForms.Edge n m)
    (x : Fin (GraphForms.dimension n m) → ℝ) : ℝ :=
  GraphForms.topDensity edges ((GraphForms.realCoordinates n m).symm x)

/-- The actual oriented normalized-chart integral. Convergence is a separate obligation. -/
def rawIntegral (edges : Fin (GraphForms.dimension n m) → GraphForms.Edge n m) : ℝ :=
  ∫ x in realDomain n m, realDensity edges x

/-- Absolute convergence of the same actual density and domain. -/
def AbsolutelyIntegrable (edges : Fin (GraphForms.dimension n m) → GraphForms.Edge n m) : Prop :=
  IntegrableOn (realDensity edges) (realDomain n m)

theorem realDensity_permute (edges : Fin (GraphForms.dimension n m) → GraphForms.Edge n m)
    (σ : Equiv.Perm (Fin (GraphForms.dimension n m))) (x : Fin (GraphForms.dimension n m) → ℝ) :
    realDensity (fun i ↦ edges (σ i)) x = (Equiv.Perm.sign σ : ℝ) * realDensity edges x := by
  exact GraphForms.topDensity_permute edges σ _

theorem rawIntegral_permute (edges : Fin (GraphForms.dimension n m) → GraphForms.Edge n m)
    (σ : Equiv.Perm (Fin (GraphForms.dimension n m))) :
    rawIntegral (fun i ↦ edges (σ i)) = (Equiv.Perm.sign σ : ℝ) * rawIntegral edges := by
  simp only [rawIntegral, realDensity_permute, integral_const_mul]

theorem rawIntegral_eq_zero_of_untargeted
    (edges : Fin (GraphForms.dimension n m) → GraphForms.Edge n m) (j : Fin m)
    (hj : ∀ a, (edges a).target ≠ Sum.inr j) : rawIntegral edges = 0 := by
  have hz : realDensity edges = 0 := by
    funext x
    exact GraphForms.topDensity_eq_zero_of_untargeted edges j hj _
  simp only [rawIntegral, hz, Pi.zero_apply, integral_zero]

/-- The outgoing-edge factorials; this does not contain the internal-vertex factorial. -/
def outgoingFactor (q : Fin (n + 1) → ℕ) : ℝ :=
  ∏ v, ((q v).factorial : ℝ)⁻¹

variable {q : Fin (n + 1) → ℕ}

/-- Real geometric edges in an explicitly specified total order of the graph's slots. -/
def orderedEdges (Γ : KontsevichGraph.General.Graph q m)
    (order : Fin (GraphForms.dimension n m) ≃ KontsevichGraph.General.Edge q) :
    Fin (GraphForms.dimension n m) → GraphForms.Edge n m :=
  fun a ↦ ⟨(order a).1, Γ.target (order a)⟩

/-- Geometric labelled weight W, including outgoing factorials and powers of 2π,
but excluding the internal-vertex MC factorial. -/
def geometricWeight (Γ : KontsevichGraph.General.Graph q m)
    (order : Fin (GraphForms.dimension n m) ≃ KontsevichGraph.General.Edge q) : ℝ :=
  outgoingFactor q * ((2 * Real.pi) ^ GraphForms.dimension n m)⁻¹ *
    rawIntegral (orderedEdges Γ order)

/-- Effective diagonal MC/star coefficient W/(n+1)!, with n+1 internal vertices. -/
def effectiveWeight (Γ : KontsevichGraph.General.Graph q m)
    (order : Fin (GraphForms.dimension n m) ≃ KontsevichGraph.General.Edge q) : ℝ :=
  effectiveMCWeight (n + 1) (geometricWeight Γ order)

/-- The canonical order is vertex-major, then outgoing-slot-major; the only
cast is the proved top-degree edge count. -/
def canonicalOrder (hq : ∑ v, q v = GraphForms.dimension n m) :
    Fin (GraphForms.dimension n m) ≃ KontsevichGraph.General.Edge q :=
  (finCongr hq.symm).trans (vertexMajorEdgeEquiv q)

def canonicalWeight (Γ : KontsevichGraph.General.Graph q m)
    (hq : ∑ v, q v = GraphForms.dimension n m) : ℝ :=
  geometricWeight Γ (canonicalOrder hq)

def canonicalEffectiveWeight (Γ : KontsevichGraph.General.Graph q m)
    (hq : ∑ v, q v = GraphForms.dimension n m) : ℝ :=
  effectiveMCWeight (n + 1) (canonicalWeight Γ hq)

theorem geometricWeight_permute (Γ : KontsevichGraph.General.Graph q m)
    (order : Fin (GraphForms.dimension n m) ≃ KontsevichGraph.General.Edge q)
    (σ : Equiv.Perm (Fin (GraphForms.dimension n m))) :
    geometricWeight Γ (σ.trans order) = (Equiv.Perm.sign σ : ℝ) * geometricWeight Γ order := by
  have he : orderedEdges Γ (σ.trans order) = fun a ↦ orderedEdges Γ order (σ a) := rfl
  simp only [geometricWeight, he, rawIntegral_permute]
  ring

/-- The missing-external-slot weight vanishes by the actual zero density,
without an integrability assumption about any other graph. -/
theorem geometricWeight_eq_zero_of_untargeted (Γ : KontsevichGraph.General.Graph q m)
    (order : Fin (GraphForms.dimension n m) ≃ KontsevichGraph.General.Edge q)
    (j : Fin m) (hj : ∀ e, Γ.target e ≠ Sum.inr j) : geometricWeight Γ order = 0 := by
  have hz := rawIntegral_eq_zero_of_untargeted (orderedEdges Γ order) j (fun a ↦ hj (order a))
  simp only [geometricWeight, hz, mul_zero]

theorem effectiveWeight_eq_zero_of_untargeted (Γ : KontsevichGraph.General.Graph q m)
    (order : Fin (GraphForms.dimension n m) ≃ KontsevichGraph.General.Edge q)
    (j : Fin m) (hj : ∀ e, Γ.target e ≠ Sum.inr j) : effectiveWeight Γ order = 0 := by
  rw [effectiveWeight, geometricWeight_eq_zero_of_untargeted Γ order j hj]
  simp [effectiveMCWeight]

theorem canonicalEffectiveWeight_eq_zero_of_untargeted
    (Γ : KontsevichGraph.General.Graph q m) (hq : ∑ v, q v = GraphForms.dimension n m)
    (j : Fin m) (hj : ∀ e, Γ.target e ≠ Sum.inr j) : canonicalEffectiveWeight Γ hq = 0 :=
  effectiveWeight_eq_zero_of_untargeted Γ (canonicalOrder hq) j hj

end EnvelopingIsomorphism.Deformation.Kontsevich.GeometricWeights
