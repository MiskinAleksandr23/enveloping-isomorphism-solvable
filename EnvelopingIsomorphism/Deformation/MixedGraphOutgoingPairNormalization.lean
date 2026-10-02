import EnvelopingIsomorphism.Deformation.BinarySplitOutgoingAverage
import EnvelopingIsomorphism.Deformation.MixedGraphPhysicalPairSums
import EnvelopingIsomorphism.Deformation.Kontsevich.VertexSplitOutgoingFactor

/-! Genuine dependent outgoing normalization of mixed physical pairs. The
correction half-factor is proved on actual split data with the two-odd sign. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
namespace EnvelopingIsomorphism.Deformation.MixedGraphOutgoingPairNormalization
open scoped Classical BigOperators
open KontsevichGraph.General KontsevichGraph.General.Graph
open KontsevichGraph.General.TwoVertexContraction
open MixedGraphProfileCarrier MixedGraphCorrectionProfiles MixedGraphInternalPairRelabelling
open MixedGraphAveraging MixedGraphPhysicalPairSums GraphCurvatureLabelCounting
open Kontsevich.GeometricWeightOutgoing
variable {n : ℕ}

private theorem ofProfile_injective {N : ℕ} {q : Fin (N + 1) → ℕ} (i : Fin (N + 1))
    (h : q = Gauge.PlacedMixedGraphTaylorCoefficients.arities 1 i) :
    Function.Injective (ofProfile (m := 2) i h) := by
  subst q
  intro Γ Δ he
  exact (Sigma.mk.inj he).2.eq

private theorem correction_pairProfile_ofProfile (p : Placement n)
    (H : Graph (vertexSplitArity (twoOddArity p.1 p.2) bivectorArity p.2) 2) :
    Correction.pairProfile p (ofProfile (expandedVector p) (splitArity p) H) =
      BinarySplitOutgoingAverage.pairProfile p.2 (selectedArity p).symm
        (fun Γ => placementSign p * canonicalQuotientWeight (k := ℝ) ⟨p,Γ⟩) H := by
  simp only [Correction.pairProfile, BinarySplitOutgoingAverage.pairProfile, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro a _
  unfold Correction.canonicalProfile BinarySplitOutgoingAverage.profile GraphCoefficientProfiles.pushforward
  apply Finset.sum_congr rfl
  intro D _
  simp only [Correction.canonicalDataGraph, (ofProfile_injective (expandedVector p) (splitArity p)).eq_iff]
  rfl

private theorem signed_correction_weight_outgoing (p : Placement n) (Γ : QuotientGraph p)
    (τ : GeneralGraphOutgoingAverage.Group (twoOddArity p.1 p.2)) :
    placementSign p * canonicalQuotientWeight (k := ℝ) ⟨p,Γ.permuteOutgoing τ⟩ =
      GeneralGraphOutgoingAverage.sign τ * (placementSign p * canonicalQuotientWeight ⟨p,Γ⟩) := by
  simp only [canonicalQuotientWeight, canonicalEffectiveWeight_permuteOutgoing, map_mul]
  simp only [GeneralGraphOutgoingAverage.sign, Algebra.algebraMap_self, RingHom.id_apply]
  ring

/-- A mixed split has precisely the signed half-quotient coefficient after
averaging every native outgoing row, including the exterior vector row. -/
theorem outgoingAverage_correction_pairProfile_split (p : Placement n) (a : Fin 2)
    (D : CorrectionSplitData p) :
    outgoingAverage (Correction.pairProfile p) (Correction.canonicalDataGraph p a D) =
      (1 / 2 : ℝ) * (placementSign p * canonicalQuotientWeight (k := ℝ) ⟨p,D.1⟩) := by
  rw [Correction.canonicalDataGraph, outgoingAverage_ofProfile]
  simp only [correction_pairProfile_ofProfile]
  exact BinarySplitOutgoingAverage.average_pairProfile_split p.2 (selectedArity p).symm
    (fun Γ => placementSign p * canonicalQuotientWeight (k := ℝ) ⟨p,Γ⟩)
    (signed_correction_weight_outgoing p) a D

/-- Removing the true quotient MC factorial and the proved sender half-factor
leaves exactly the signed raw integral, with no normalization assumption. -/
theorem outgoingAverage_correction_pairProfile_split_raw (p : Placement n) (a : Fin 2)
    (D : CorrectionSplitData p) :
    (2 * (n + 2).factorial : ℕ) *
      outgoingAverage (Correction.pairProfile p) (Correction.canonicalDataGraph p a D) =
        placementSign p * rawCorrectionQuotientWeight ⟨p,D.1⟩ := by
  rw [outgoingAverage_correction_pairProfile_split]
  have hw : canonicalQuotientWeight (k := ℝ) ⟨p,D.1⟩ = ((n + 2).factorial : ℝ)⁻¹ *
      rawCorrectionQuotientWeight ⟨p,D.1⟩ := by
    simp only [canonicalQuotientWeight, rawCorrectionQuotientWeight,
      Kontsevich.GeometricWeights.canonicalEffectiveWeight]
    simp [Kontsevich.effectiveMCWeight, Rat.smul_def]
  rw [hw]
  have hf : ((n + 2).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (n + 2)
  push_cast
  field_simp

/-- The actual split arities have the geometric 3/2 outgoing-factor ratio,
with the exterior vector vertex preserved. -/
theorem correction_split_outgoingFactor (p : Placement n) :
    Kontsevich.GeometricWeights.outgoingFactor
      (Gauge.PlacedMixedGraphTaylorCoefficients.arities 1 (expandedVector p)) =
        (3 / 2 : ℝ) * Kontsevich.GeometricWeights.outgoingFactor (twoOddArity p.1 p.2) := by
  calc
    _ = Kontsevich.GeometricWeights.outgoingFactor
        (vertexSplitArity (twoOddArity p.1 p.2) bivectorArity p.2) :=
      congrArg Kontsevich.GeometricWeights.outgoingFactor (splitArity p).symm
    _ = _ := Kontsevich.VertexSplitOutgoingFactor.bivector_split_factor
      (twoOddArity p.1 p.2) p.2 (selectedArity p).symm

/-- The actual source split has outgoing-factor ratio one. -/
theorem source_split_outgoingFactor (i : Fin (n + 1)) :
    Kontsevich.GeometricWeights.outgoingFactor
      (Gauge.PlacedMixedGraphTaylorCoefficients.arities 1 (vertexSplitChild i 0)) =
        Kontsevich.GeometricWeights.outgoingFactor (fun _ : Fin (n + 1) => 2) := by
  calc
    _ = Kontsevich.GeometricWeights.outgoingFactor
        (vertexSplitArity (fun _ : Fin (n + 1) => 2) vectorBivectorArity i) :=
      congrArg Kontsevich.GeometricWeights.outgoingFactor (MixedGraphActionSplits.actionSplitArity i).symm
    _ = _ := Kontsevich.VertexSplitOutgoingFactor.vector_bivector_split_factor
      (fun _ : Fin (n + 1) => 2) i rfl

/-- The full native outgoing physical source coefficient. -/
def sourcePhysicalCoefficient (H : VectorGraph (n + 1) 2) (T : PhysicalPair n) : ℝ :=
  ((2 : ℝ)^(n + 1))⁻¹ * ∑ τ : OutgoingGroup (n + 1), outgoingSign (k := ℝ) τ *
    rawSourcePairCoefficient ((outgoingGraphEquiv τ 2).symm H) T

/-- The full outgoing physical correction coefficient, with the binary
sender normalization removed. The raw fibre keeps its actual two-odd sign. -/
def correctionPhysicalCoefficient (H : VectorGraph (n + 2) 2) (T : PhysicalPair (n + 1)) : ℝ :=
  2 * ((2 : ℝ)^(n + 2))⁻¹ * ∑ τ : OutgoingGroup (n + 2), outgoingSign (k := ℝ) τ *
    rawCorrectionPairCoefficient ((outgoingGraphEquiv τ 2).symm H) T

/-- The literal unordered child pair of a mixed correction placement. -/
def correctionChildPair (p : Placement n) : PhysicalPair (n + 1) :=
  ⟨childPair (n := n + 1) p.2.val, card_childPair (n := n + 1) p.2.val⟩

private def correctionIdentityLabel (p : Placement n) :
    MixedGraphPairLabelCounting.CorrectionPairLabels (correctionChildPair p) (expandedVector p) :=
  ⟨p, ⟨⟨Equiv.refl _, fun _ => Iff.rfl⟩, rfl⟩⟩

/-- The full physical coefficient on an actual split is its true signed raw
quotient integral. Thus the removed sender normalizer is computed, not assumed. -/
theorem correctionPhysicalCoefficient_split (p : Placement n) (a : Fin 2)
    (D : CorrectionSplitData p) :
    correctionPhysicalCoefficient (Correction.canonicalDataGraph p a D) (correctionChildPair p) =
      placementSign p * rawCorrectionQuotientWeight ⟨p,D.1⟩ := by
  have he (τ : OutgoingGroup (n + 2)) :
      rawCorrectionPairCoefficient
        ((outgoingGraphEquiv τ 2).symm (Correction.canonicalDataGraph p a D)) (correctionChildPair p) =
      ((n + 2).factorial : ℝ) * Correction.pairProfile p
        ((outgoingGraphEquiv τ 2).symm (Correction.canonicalDataGraph p a D)) := by
    have h := rawCorrectionPairCoefficient_eq_scaled
      ((outgoingGraphEquiv τ 2).symm (Correction.canonicalDataGraph p a D))
      (correctionChildPair p) (correctionIdentityLabel p)
    simpa only [correctionIdentityLabel, MixedGraphBlockRelabelling.internalGraphEquiv_symm_apply,
      Equiv.refl_symm, MixedGraphBlockRelabelling.internalGraphEquiv_refl] using h
  calc
    _ = (2 * (n + 2).factorial : ℕ) *
        outgoingAverage (Correction.pairProfile p) (Correction.canonicalDataGraph p a D) := by
      simp only [correctionPhysicalCoefficient, he, outgoingAverage_apply, Finset.mul_sum,
        Nat.cast_mul, Nat.cast_ofNat]
      apply Finset.sum_congr rfl
      intro τ _
      ring
    _ = _ := outgoingAverage_correction_pairProfile_split_raw p a D

/-- The actual outgoing orbit of each split has the full-family permutation
sign multiplying the same half-weight, including the original placement sign. -/
theorem outgoingAverage_correction_pairProfile_split_permute (p : Placement n) (a : Fin 2)
    (D : CorrectionSplitData p)
    (τ : GeneralGraphOutgoingAverage.Group (vertexSplitArity (twoOddArity p.1 p.2) bivectorArity p.2)) :
    outgoingAverage (Correction.pairProfile p)
      (ofProfile (expandedVector p) (splitArity p)
        ((D.1.vertexSplit (BinaryVertexContraction.canonicalTemplate a) p.2
          (selectedArity p).symm D.2).permuteOutgoing τ)) =
      GeneralGraphOutgoingAverage.sign τ * ((1 / 2 : ℝ) *
        (placementSign p * canonicalQuotientWeight (k := ℝ) ⟨p,D.1⟩)) := by
  rw [outgoingAverage_ofProfile]
  simp only [correction_pairProfile_ofProfile]
  change GeneralGraphOutgoingAverage.average _ _ = _
  rw [GeneralGraphOutgoingAverage.average_permuteOutgoing]
  congr 1
  exact BinarySplitOutgoingAverage.average_pairProfile_split p.2 (selectedArity p).symm
    (fun Γ => placementSign p * canonicalQuotientWeight (k := ℝ) ⟨p,Γ⟩)
    (signed_correction_weight_outgoing p) a D

/-- Exact physical source endpoint, using full outgoing physical coefficients. -/
theorem boundaryAverage_source_eq_physical (H : VectorGraph (n + 1) 2) :
    boundaryAverage (MixedGraphActionSplits.sourceActionProfile
      (GraphBoundaryProfiles.canonicalBinaryWeight (k := ℝ) (n + 1))) H =
      ((n + 2).factorial : ℝ)⁻¹ * ∑ T : PhysicalPair n, sourcePhysicalCoefficient H T := by
  rw [boundaryAverage_canonical_source_eq_pairs]
  simp only [sourcePhysicalCoefficient, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro T _
  apply Finset.sum_congr rfl
  intro τ _
  ring

/-- Exact physical correction endpoint. Its 3/2 coefficient combines the
proved cyclic collapse, exchanged-child fibre and sender half-factor. -/
theorem boundaryAverage_correction_eq_physical (H : VectorGraph (n + 2) 2) :
    boundaryAverage (correctionProfile (canonicalQuotientWeight (k := ℝ))) H =
      (3 / 2 : ℝ) * ((n + 3).factorial : ℝ)⁻¹ *
        ∑ T : PhysicalPair (n + 1), correctionPhysicalCoefficient H T := by
  rw [boundaryAverage_canonical_correction_eq_pairs]
  simp only [correctionPhysicalCoefficient, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro T _
  apply Finset.sum_congr rfl
  intro τ _
  ring

end EnvelopingIsomorphism.Deformation.MixedGraphOutgoingPairNormalization
