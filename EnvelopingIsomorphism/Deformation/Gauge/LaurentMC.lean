import EnvelopingIsomorphism.Deformation.Gauge.LaurentConjugation
import EnvelopingIsomorphism.Deformation.Gauge.AssociativeMC

/-! The actual near-identity gauge action preserves the complete Laurent
full-cochain MC locus. Each coefficient has its own Laurent lower bound. -/

noncomputable section

set_option maxSynthPendingDepth 3

namespace EnvelopingIsomorphism.Deformation.Gauge.LaurentConjugation

open EnvelopingIsomorphism.FormalSeries PowerSeriesModule

universe u v
variable {k : Type u} [CommRing k] {A : Type v} [AddCommGroup A] [Module k A]

abbrev MC (μ : BinaryCoefficients (k := k) (A := A)) :=
  MCSeries (LaurentModule.differentialBinarySeries μ) (LaurentModule.insertBinarySeries (k := k) (A := A))

/-- Faithful embedding in the actual Hochschild MC locus of Laurent-valued functions. -/
def mcEmbed (μ : BinaryCoefficients (k := k) (A := A)) :
    MC μ → AssociativeMC (evaluateCoefficient μ) :=
  associativeMCEmbed (LaurentModule.differentialBinarySeries μ) LaurentModule.insertBinarySeries
    evaluateCoefficient LaurentModule.ternaryEvaluation (evaluateCoefficient μ)
    (LaurentModule.ternaryEvaluation_differentialBinarySeries μ)
    LaurentModule.ternaryEvaluation_insertBinary

@[simp] theorem mcEmbed_val (μ : BinaryCoefficients (k := k) (A := A)) (b : MC μ) :
    (mcEmbed μ b).val = embed b.val := rfl

theorem mcEmbed_injective (μ : BinaryCoefficients (k := k) (A := A)) :
    Function.Injective (mcEmbed μ) := by
  intro b c h
  exact Subtype.ext (embed_injective (congrArg Subtype.val h))

theorem mc_iff_associative (μ : BinaryCoefficients (k := k) (A := A))
    (hμ : ∀ a b c, evaluateCoefficient μ (evaluateCoefficient μ a b) c =
      evaluateCoefficient μ a (evaluateCoefficient μ b c)) (b : Families (k := k) (A := A)) :
    quadraticCurvature (LaurentModule.differentialBinarySeries μ) LaurentModule.insertBinarySeries b = 0 ↔
      ∀ p q r, evaluateFamily (single 0 μ + b) (evaluateFamily (single 0 μ + b) p q) r =
        evaluateFamily (single 0 μ + b) p (evaluateFamily (single 0 μ + b) q r) := by
  have h := quadratic_MC_iff_associative_of_embedding
    (LaurentModule.differentialBinarySeries μ) LaurentModule.insertBinarySeries
    evaluateCoefficient LaurentModule.ternaryEvaluation LaurentModule.ternaryEvaluation_injective
    (evaluateCoefficient μ) hμ (LaurentModule.ternaryEvaluation_differentialBinarySeries μ)
    LaurentModule.ternaryEvaluation_insertBinary b
  simpa only [evaluateFamily, embed, map_add, map_single] using h

/-- Full product conjugation expressed in its positive Laurent coefficient coordinates. -/
def transportFamily (μ : BinaryCoefficients (k := k) (A := A))
    (G : GaugeUnit (OperatorRing (k := k) (A := A))) (b : Families (k := k) (A := A)) :
    Families (k := k) (A := A) :=
  conjugateFamily G.val (single 0 μ + b) - single 0 μ

theorem embed_transportFamily (μ : BinaryCoefficients (k := k) (A := A))
    (G : GaugeUnit (OperatorRing (k := k) (A := A))) (b : Families (k := k) (A := A)) :
    embed (transportFamily μ G b) =
      conjugateBinarySeries (ambientGauge G).val (single 0 (evaluateCoefficient μ) + embed b) -
        single 0 (evaluateCoefficient μ) := by
  rw [transportFamily, map_sub, embed_conjugateFamily]
  simp only [embed, map_add, map_single]
  rfl

/-- An actual action on MC elements, obtained by proving that the closed
coefficient conjugation satisfies the MC equation. -/
def transport (μ : BinaryCoefficients (k := k) (A := A))
    (hμ : ∀ a b c, evaluateCoefficient μ (evaluateCoefficient μ a b) c =
      evaluateCoefficient μ a (evaluateCoefficient μ b c))
    (G : GaugeUnit (OperatorRing (k := k) (A := A))) (b : MC μ) : MC μ :=
  ⟨transportFamily μ G b.val, by
    rw [transportFamily, coeffV_sub, conjugateFamily_agree G.val _ G.near_one 0 (by decide)]
    simp only [coeffV_add, b.property.1, add_zero, sub_self], by
    apply seriesMap_injective LaurentModule.ternaryEvaluation LaurentModule.ternaryEvaluation_injective
    rw [map_zero, curvature_embedding (LaurentModule.differentialBinarySeries μ)
      LaurentModule.insertBinarySeries evaluateCoefficient LaurentModule.ternaryEvaluation
      (evaluateCoefficient μ) (LaurentModule.ternaryEvaluation_differentialBinarySeries μ)
      LaurentModule.ternaryEvaluation_insertBinary]
    change quadraticCurvature _ _ (embed (transportFamily μ G b.val)) = 0
    rw [embed_transportFamily]
    exact (associativeMCTransport (evaluateCoefficient μ) hμ (ambientGauge G) (mcEmbed μ b)).property.2⟩

@[simp] theorem transport_val (μ : BinaryCoefficients (k := k) (A := A))
    (hμ : ∀ a b c, evaluateCoefficient μ (evaluateCoefficient μ a b) c =
      evaluateCoefficient μ a (evaluateCoefficient μ b c))
    (G : GaugeUnit (OperatorRing (k := k) (A := A))) (b : MC μ) :
    (transport μ hμ G b).val = transportFamily μ G b.val := rfl

theorem mcEmbed_transport (μ : BinaryCoefficients (k := k) (A := A))
    (hμ : ∀ a b c, evaluateCoefficient μ (evaluateCoefficient μ a b) c =
      evaluateCoefficient μ a (evaluateCoefficient μ b c))
    (G : GaugeUnit (OperatorRing (k := k) (A := A))) (b : MC μ) :
    mcEmbed μ (transport μ hμ G b) =
      associativeMCTransport (evaluateCoefficient μ) hμ (ambientGauge G) (mcEmbed μ b) :=
  Subtype.ext (embed_transportFamily μ G b.val)

@[simp] theorem transport_one (μ : BinaryCoefficients (k := k) (A := A))
    (hμ : ∀ a b c, evaluateCoefficient μ (evaluateCoefficient μ a b) c =
      evaluateCoefficient μ a (evaluateCoefficient μ b c)) (b : MC μ) :
    transport μ hμ 1 b = b := by
  apply mcEmbed_injective μ
  rw [mcEmbed_transport, map_one, associativeMCTransport_one]

theorem transport_mul (μ : BinaryCoefficients (k := k) (A := A))
    (hμ : ∀ a b c, evaluateCoefficient μ (evaluateCoefficient μ a b) c =
      evaluateCoefficient μ a (evaluateCoefficient μ b c))
    (G H : GaugeUnit (OperatorRing (k := k) (A := A))) (b : MC μ) :
    transport μ hμ (G * H) b = transport μ hμ G (transport μ hμ H b) := by
  apply mcEmbed_injective μ
  rw [mcEmbed_transport, mcEmbed_transport, mcEmbed_transport, map_mul, associativeMCTransport_mul]

@[reducible] def mcMulAction (μ : BinaryCoefficients (k := k) (A := A))
    (hμ : ∀ a b c, evaluateCoefficient μ (evaluateCoefficient μ a b) c =
      evaluateCoefficient μ a (evaluateCoefficient μ b c)) :
    MulAction (GaugeUnit (OperatorRing (k := k) (A := A))) (MC μ) where
  smul := transport μ hμ
  one_smul := transport_one μ hμ
  mul_smul := transport_mul μ hμ

theorem transport_agree (μ : BinaryCoefficients (k := k) (A := A))
    (hμ : ∀ a b c, evaluateCoefficient μ (evaluateCoefficient μ a b) c =
      evaluateCoefficient μ a (evaluateCoefficient μ b c))
    (G : GaugeUnit (OperatorRing (k := k) (A := A))) (b : MC μ)
    {N : ℕ} (hG : NearIdentity N G.series) :
    AgreeBelow N (transport μ hμ G b).val b.val := by
  intro n hn
  rw [transport_val, transportFamily, coeffV_sub, conjugateFamily_agree G.val _ hG n hn, coeffV_add]
  abel

/-- The degree-zero Hochschild differential is itself a closed Laurent operator. -/
def differentialUnary (μ : BinaryCoefficients (k := k) (A := A)) :
    OperatorCoefficients (k := k) (A := A) →ₗ[Scalars (k := k)] BinaryCoefficients (k := k) (A := A) :=
  -(unaryCoefficientAction (k := k) (A := A)).flip μ

theorem evaluate_differentialUnary (μ : BinaryCoefficients (k := k) (A := A))
    (F : OperatorCoefficients (k := k) (A := A)) :
    evaluateCoefficient (differentialUnary μ F) =
      differentialOne (evaluateCoefficient μ) (evaluateOperator F) := by
  change evaluateCoefficient (-unaryCoefficientAction F μ) = _
  rw [map_neg, evaluate_unaryCoefficientAction, differentialOne_eq_neg_unaryAction]
  rfl

theorem transport_leading (μ : BinaryCoefficients (k := k) (A := A))
    (hμ : ∀ a b c, evaluateCoefficient μ (evaluateCoefficient μ a b) c =
      evaluateCoefficient μ a (evaluateCoefficient μ b c))
    (G : GaugeUnit (OperatorRing (k := k) (A := A))) (b : MC μ)
    {N : ℕ} (hN : 0 < N) (hG : NearIdentity N G.series) :
    coeffV N (transport μ hμ G b).val - coeffV N b.val =
      -differentialUnary μ (operatorCoordinates (PowerSeries.coeff N G.series)) := by
  apply LaurentModule.binaryEvaluation_injective
  have h := associativeMCTransport_leading (evaluateCoefficient μ) hμ (ambientGauge G) (mcEmbed μ b)
    hN (near_ambientOperators hG)
  rw [← mcEmbed_transport] at h
  change evaluateCoefficient (coeffV N (transport μ hμ G b).val) - evaluateCoefficient (coeffV N b.val) =
    -differentialOne (evaluateCoefficient μ) (LaurentOperator.actionHom (PowerSeries.coeff N G.series)) at h
  change evaluateCoefficient _ = evaluateCoefficient _
  rw [map_sub, map_neg, evaluate_differentialUnary, evaluateOperator_coordinates]
  exact h

end EnvelopingIsomorphism.Deformation.Gauge.LaurentConjugation
