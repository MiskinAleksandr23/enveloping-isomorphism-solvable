import EnvelopingIsomorphism.Deformation.GraphBoundaryProfiles
import EnvelopingIsomorphism.Deformation.Kontsevich.GeometricWeightRelabel

/-! Canonical binary weights with the internal-vertex MC factorial separated.
The true nullary coefficient and every internal relabelling are included. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.GraphCanonicalBinaryWeights
open scoped BigOperators Classical
open UniformBinaryGraphs GraphBoundaryProfiles
open Kontsevich.GeometricWeights

/-- Only the internal vertex factorial is removed; outgoing-slot and angle
normalizations remain in the genuine geometric integral. -/
def rawBinaryWeight : (n : ℕ) → BinaryGraph n 2 → ℝ
  | 0, _ => 1
  | n + 1, Γ => canonicalWeight Γ (binaryEdgeCount n)

/-- This includes the actual multiplication coefficient at zero vertices. -/
theorem canonicalBinaryWeight_eq_factorial (n : ℕ) (Γ : BinaryGraph n 2) :
    canonicalBinaryWeight (k := ℝ) n Γ = (n.factorial : ℝ)⁻¹ * rawBinaryWeight n Γ := by
  cases n with
  | zero => simp [canonicalBinaryWeight, rawBinaryWeight]
  | succ n =>
    simp only [canonicalBinaryWeight, binaryWeightOver, binaryWeight,
      ofBinary_toLegacy, rawBinaryWeight, canonicalEffectiveWeight]
    simp [Kontsevich.effectiveMCWeight, Rat.smul_def]

/-- The raw integral is invariant under every actual internal graph permutation. -/
theorem rawBinaryWeight_permuteInternal (n : ℕ) (Γ : BinaryGraph n 2)
    (σ : Equiv.Perm (Fin n)) :
    rawBinaryWeight n (Γ.permuteInternal σ) = rawBinaryWeight n Γ := by
  cases n with
  | zero => rfl
  | succ n =>
    simpa only [rawBinaryWeight, KontsevichGraph.General.Graph.permuteProfile_uniform] using
      canonicalWeight_permuteProfile_binary Γ (binaryEdgeCount n) σ

/-- Both outgoing normalization and the internal MC factorial are preserved. -/
theorem canonicalBinaryWeight_permuteInternal (n : ℕ) (Γ : BinaryGraph n 2)
    (σ : Equiv.Perm (Fin n)) :
    canonicalBinaryWeight (k := ℝ) n (Γ.permuteInternal σ) =
      canonicalBinaryWeight (k := ℝ) n Γ := by
  rw [canonicalBinaryWeight_eq_factorial, canonicalBinaryWeight_eq_factorial,
    rawBinaryWeight_permuteInternal]

/-- Scalar normalizations factor through the actual graft-data sum. -/
theorem graftProfile_smul_weights {k : Type*} [CommRing k] {a b : ℕ}
    (r : Fin 2) (s t : k) (w : BinaryGraph a 2 → k) (v : BinaryGraph b 2 → k) :
    GraphWeightedInsertion.graftProfile r (s • w) (t • v) =
      (s * t) • GraphWeightedInsertion.graftProfile r w v := by
  funext H
  simp only [GraphWeightedInsertion.graftProfile, GraphCoefficientProfiles.pushforward,
    Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro D hD
  split_ifs <;> ring

/-- Both MC factorials in an actual associator summand are separated without
changing any graft assignment, including empty factors. -/
theorem canonical_graftProfile {a b : ℕ} (r : Fin 2) :
    GraphWeightedInsertion.graftProfile r
        (canonicalBinaryWeight (k := ℝ) a) (canonicalBinaryWeight (k := ℝ) b) =
      ((a.factorial : ℝ)⁻¹ * (b.factorial : ℝ)⁻¹) •
        GraphWeightedInsertion.graftProfile r (rawBinaryWeight a) (rawBinaryWeight b) := by
  have h (n : ℕ) : canonicalBinaryWeight (k := ℝ) n =
      (n.factorial : ℝ)⁻¹ • rawBinaryWeight n := by
    funext Γ
    exact canonicalBinaryWeight_eq_factorial n Γ
  rw [h a, h b, graftProfile_smul_weights]

end EnvelopingIsomorphism.Deformation.GraphCanonicalBinaryWeights
