import EnvelopingIsomorphism.Rees.StarComparison
import EnvelopingIsomorphism.Deformation.GraphPBWComparison

/-! The coherent graph comparisons and the actual Rees operator determine one
marked gauge element. Equality at the special fiber is proved from the Rees marking. -/

noncomputable section

namespace EnvelopingIsomorphism.Rees.GraphStarComparison

open FormalSeries CompletedOperator
open scoped CompletedOperator

variable {k : Type*} [Field k] [CharZero k] {n : ℕ}
    {L M : Type*} [LieRing L] [LieAlgebra k L] [LieRing M] [LieAlgebra k M]
    {bL : Module.Basis (Fin n) k L} {bM : Module.Basis (Fin n) k M}
    (dL : WeightData bL) (dM : WeightData bM)
    (Φ : UniversalEnvelopingAlgebra k L ≃ₐ[k] UniversalEnvelopingAlgebra k M)
    (hw : dL.weight = dM.weight)
    (hΦ : EnvelopingFamily.LeadingGenerators dL dM Φ.toAlgHom)
    (hΦ' : EnvelopingFamily.LeadingGenerators dM dL Φ.symm.toAlgHom)

include Φ hw hΦ hΦ' in
omit [CharZero k] in
/-- The actual prescribed zero-fiber Lie identification forces equal specialized
structure coefficients. No separate assumption of common zero tensor is needed. -/
theorem zero_coeff_eq (i j r : Fin n) :
    Polynomial.eval 0 (dL.coeff i j r) = Polynomial.eval 0 (dM.coeff i j r) := by
  rw [← Family.fiber_structureCoeff, ← Family.fiber_structureCoeff]
  have h := (EnvelopingFamily.zeroLieEquiv dL dM Φ hw hΦ hΦ').map_lie
    (Family.fiberBasis dL 0 i) (Family.fiberBasis dL 0 j)
  rw [EnvelopingFamily.zeroLieEquiv_basis, EnvelopingFamily.zeroLieEquiv_basis] at h
  have hr := congrArg (fun x ↦ (Family.fiberBasis dM 0).repr x r) h
  change (Family.fiberBasis dM 0).repr
      ((EnvelopingFamily.zeroLieEquiv dL dM Φ hw hΦ hΦ').toLinearEquiv
        ⁅Family.fiberBasis dL 0 i, Family.fiberBasis dL 0 j⁆) r = _ at hr
  rw [EnvelopingFamily.zeroLieEquiv_toLinearEquiv] at hr
  simpa [Module.Basis.equiv] using hr

/-- Rees coefficients are constant in the inner polynomial variable; the graph
comparison itself inserts the single factor of the inner parameter. -/
def tensor (d : WeightData bL) : Fin n → Fin n → Fin n → Polynomial (Polynomial k) :=
  fun i j r ↦ Polynomial.C (d.coeff i j r)

variable
    (s : (j : ℕ) → Finset (Deformation.KontsevichGraph (j + 1)))
    (w : (j : ℕ) → Deformation.KontsevichGraph (j + 1) → Polynomial (Polynomial k))

/-- The actual averaged PBW-to-graph comparison, as a true completed operator unit. -/
def comparison (d : WeightData bL) :
    (Operators k (PolynomialCoefficientOperators.Coordinates (Fin n) k))ˣ :=
  Deformation.KontsevichGraph.comparisonCompletedUnit s w (tensor d)

include Φ hw hΦ hΦ' in
theorem comparison_constantCoeff :
    PowerSeries.constantCoeff (comparison s w dL : Operators k
      (PolynomialCoefficientOperators.Coordinates (Fin n) k)) =
    PowerSeries.constantCoeff (comparison s w dM : Operators k
      (PolynomialCoefficientOperators.Coordinates (Fin n) k)) := by
  simp only [comparison, Deformation.KontsevichGraph.comparisonCompletedUnit_val]
  apply Deformation.KontsevichGraph.comparisonCompleted_constant_eq
  intro i j r
  change Polynomial.map (Polynomial.evalRingHom 0) (Polynomial.C (dL.coeff i j r)) =
    Polynomial.map (Polynomial.evalRingHom 0) (Polynomial.C (dM.coeff i j r))
  simp only [Polynomial.map_C, Polynomial.coe_evalRingHom]
  rw [zero_coeff_eq dL dM Φ hw hΦ hΦ' i j r]

/-- One actual marked gauge element, with both graph factors chosen by the same
universal graph formula and with the middle factor constructed in E2/E3. -/
def gauge : Deformation.Gauge.GaugeUnit
    (LaurentSeries (Module.End k (PolynomialCoefficientOperators.Coordinates (Fin n) k))) :=
  StarComparison.ofReesGauge dL dM Φ hw hΦ hΦ' (comparison s w dL) (comparison s w dM)
    (comparison_constantCoeff dL dM Φ hw hΦ hΦ' s w)

theorem gauge_series :
    (gauge dL dM Φ hw hΦ hΦ' s w).series =
      (comparison s w dM : Operators k (PolynomialCoefficientOperators.Coordinates (Fin n) k)) *
        UniformBound.completedOperator dL dM Φ hw hΦ hΦ' *
          (↑((comparison s w dL)⁻¹) : Operators k
            (PolynomialCoefficientOperators.Coordinates (Fin n) k)) := by
  simp only [gauge, StarComparison.ofReesGauge, StarComparison.conjugatedGauge_series,
    StarComparison.conjugatedUnit_val, UniformBound.completedUnit_val]

end EnvelopingIsomorphism.Rees.GraphStarComparison
