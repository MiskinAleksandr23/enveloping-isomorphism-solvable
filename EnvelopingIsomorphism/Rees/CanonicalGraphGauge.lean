import EnvelopingIsomorphism.Rees.CanonicalGraphBase
import EnvelopingIsomorphism.Deformation.Gauge.CanonicalGraphMC
import EnvelopingIsomorphism.Rees.GraphProductAssociativity

/-! The actual canonical Rees gauge acts on the actual canonical Taylor images.
All common-base and parameter-weight identifications are explicit. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

namespace EnvelopingIsomorphism.Rees.CanonicalGraphGauge

open EnvelopingIsomorphism.Deformation EnvelopingIsomorphism.FormalSeries
open Gauge PowerSeriesModule

variable {k L M : Type*} [Field k] [CharZero k] [Algebra ℝ k]
  [LieRing L] [LieAlgebra k L] [LieRing M] [LieAlgebra k M]
  (D : Identification.RecoveredData k L M)

local instance : CharZero (LaurentSeries k) := LaurentSchouten.scalarCharZero

abbrev SourceMC := ReflectionSource.MC D
abbrev MCIdentity := CanonicalGraph.MCIdentity k D.size (CanonicalTangent.baseCoefficient D)
  (CanonicalTangent.base_isMaurerCartan D)

abbrev taylor := CanonicalGraph.taylor k D.size (CanonicalTangent.baseCoefficient D)

variable (hμ : CanonicalTangent.StarAssociative D) (hMC : MCIdentity D)

def quantize (b : SourceMC D) : LaurentConjugation.TargetMC (CanonicalTangent.baseStar D) hμ :=
  CanonicalGraph.quantize k D.size (CanonicalTangent.baseCoefficient D)
    (CanonicalTangent.base_isMaurerCartan D) hμ hMC b

@[simp] theorem quantize_val (b : SourceMC D) :
    (quantize D hμ hMC b).val = taylorApply (taylor D) b.val := rfl

theorem source_taylor_eq_full_sub_base :
    taylorApply (taylor D) (ReflectionSource.source D).val =
      GraphTaylorIdentification.fullTaylor D.sourceWeightData
        (fun _ ↦ Finset.univ) (Kontsevich.GeometricWeights.binaryWeightOver k) -
      single 0 (CanonicalTangent.baseStar D) := by
  change taylorApply
    (laurentPlacementTaylorFamily
      (GraphTaylorCoefficients.effectiveFamily (fun _ ↦ Finset.univ)
        (Kontsevich.GeometricWeights.binaryWeightOver k))
      (PoissonMCFamily.constantBivector D.sourceWeightData))
    (PoissonMCFamily.perturbationSeries D.sourceWeightData) = _
  rw [GraphTaylorIdentification.taylorApply_eq_graph_difference,
    ← GraphTaylorIdentification.fullTaylor_eq_nativeGraphFamily,
    CanonicalGraphBase.source_constantCoeff]

theorem target_taylor_eq_full_sub_base :
    taylorApply (taylor D) (ReflectionSource.target D).val =
      GraphTaylorIdentification.fullTaylor D.targetWeightData
        (fun _ ↦ Finset.univ) (Kontsevich.GeometricWeights.binaryWeightOver k) -
      single 0 (CanonicalTangent.baseStar D) := by
  change taylorApply
    (laurentPlacementTaylorFamily
      (GraphTaylorCoefficients.effectiveFamily (fun _ ↦ Finset.univ)
        (Kontsevich.GeometricWeights.binaryWeightOver k))
      (PoissonMCFamily.constantBivector D.sourceWeightData))
    (PoissonMCFamily.perturbationSeries D.targetWeightData) = _
  rw [RecoveredPoissonMC.constantBivector_eq D,
    GraphTaylorIdentification.taylorApply_eq_graph_difference,
    ← GraphTaylorIdentification.fullTaylor_eq_nativeGraphFamily,
    CanonicalGraphBase.target_constantCoeff]

/-- The genuine marked J_M Φ J_L⁻¹, in native polynomial operator coordinates. -/
def gauge : GaugeUnit (CanonicalGraph.OperatorRing k D.size) :=
  NativeGraphTaylorGauge.gauge D.sourceWeightData D.targetWeightData
    CanonicalGraphBase.higherSets
    (NativeGraphTaylorGauge.parameterHigher (CanonicalGraphBase.higherWeights (k := k)))
    D.equiv rfl D.forward_leading D.inverse_leading

local instance : MulAction (GaugeUnit (CanonicalGraph.OperatorRing k D.size))
    (LaurentConjugation.TargetMC (CanonicalTangent.baseStar D) hμ) :=
  LaurentConjugation.targetMulAction (CanonicalTangent.baseStar D) hμ

theorem gauge_transports_of_productLaws
    (lawsL : GeometricStarComparison.ProductLaws CanonicalGraphBase.higherSets
      (NativeGraphTaylorGauge.parameterHigher (CanonicalGraphBase.higherWeights (k := k)))
      D.sourceWeightData)
    (lawsM : GeometricStarComparison.ProductLaws CanonicalGraphBase.higherSets
      (NativeGraphTaylorGauge.parameterHigher (CanonicalGraphBase.higherWeights (k := k)))
      D.targetWeightData) :
    gauge D • quantize D hμ hMC (ReflectionSource.source D) =
      quantize D hμ hMC (ReflectionSource.target D) := by
  apply Subtype.ext
  have h := NativeGraphTaylorGauge.gauge_transports_taylor D.sourceWeightData D.targetWeightData
    CanonicalGraphBase.higherSets D.equiv rfl D.forward_leading D.inverse_leading
    (CanonicalGraphBase.higherWeights (k := k)) lawsL lawsM
  rw [CanonicalGraphBase.geometricFirstSets_univ, CanonicalGraphBase.geometricFirstWeights_canonical,
    CanonicalGraphBase.source_constantCoeff] at h
  exact h

include hμ hMC in
/-- The actual source finite product laws follow from the graph MC identity;
they are not additional inputs to the final comparison. -/
theorem source_productLaws :
    GeometricStarComparison.ProductLaws CanonicalGraphBase.higherSets
      (NativeGraphTaylorGauge.parameterHigher (CanonicalGraphBase.higherWeights (k := k)))
      D.sourceWeightData := by
  apply GraphProductAssociativity.geometricProductLaws_of_nativeMC D.sourceWeightData
    (CanonicalTangent.baseStar D) hμ
  have h := hMC (ReflectionSource.source D)
  change quadraticCurvature (LaurentModule.differentialBinarySeries (CanonicalTangent.baseStar D))
    LaurentModule.insertBinarySeries (taylorApply (taylor D) (ReflectionSource.source D).val) = 0 at h
  rw [source_taylor_eq_full_sub_base] at h
  exact h

include hμ hMC in
/-- The target product laws follow from the same MC identity at the common source base. -/
theorem target_productLaws :
    GeometricStarComparison.ProductLaws CanonicalGraphBase.higherSets
      (NativeGraphTaylorGauge.parameterHigher (CanonicalGraphBase.higherWeights (k := k)))
      D.targetWeightData := by
  apply GraphProductAssociativity.geometricProductLaws_of_nativeMC D.targetWeightData
    (CanonicalTangent.baseStar D) hμ
  have h := hMC (ReflectionSource.target D)
  change quadraticCurvature (LaurentModule.differentialBinarySeries (CanonicalTangent.baseStar D))
    LaurentModule.insertBinarySeries (taylorApply (taylor D) (ReflectionSource.target D).val) = 0 at h
  rw [target_taylor_eq_full_sub_base] at h
  exact h

/-- The genuine native Rees gauge transports the canonical MC images. The only
inputs are base associativity and the explicit canonical graph MC identity. -/
theorem gauge_transports :
    gauge D • quantize D hμ hMC (ReflectionSource.source D) =
      quantize D hμ hMC (ReflectionSource.target D) :=
  gauge_transports_of_productLaws D hμ hMC (source_productLaws D hμ hMC) (target_productLaws D hμ hMC)

end EnvelopingIsomorphism.Rees.CanonicalGraphGauge
