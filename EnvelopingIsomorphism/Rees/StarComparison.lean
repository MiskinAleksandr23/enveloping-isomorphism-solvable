import EnvelopingIsomorphism.FormalSeries.CompletedOperatorAction
import EnvelopingIsomorphism.Deformation.LowArity
import EnvelopingIsomorphism.Deformation.Gauge.UnitGroup
import EnvelopingIsomorphism.Rees.CompletedComparisonData

/-!
# Assembly of the completed star comparison

The algebraic composition and inverse arguments take place in the genuine ring of Laurent
operator coefficients with an outer power-series parameter. The algebraic assembly below is
separate from the proofs that the concrete PBW and graph products satisfy its input equations.
-/

noncomputable section

namespace EnvelopingIsomorphism.Rees.StarComparison

open EnvelopingIsomorphism.FormalSeries
open CompletedOperator
open scoped CompletedOperator

section Assembly

variable {k A : Type*} [CommRing k] [AddCommGroup A] [Module k A]

/-- An actual invertible series intertwines the two completed binary products. -/
def Intertwines (F : (Operators k A)ˣ)
    (μ ν : Deformation.Binary (PowerSeries (LaurentSeries k)) (Vectors k A)) : Prop :=
  ∀ x y, actionEquiv F (μ x y) = ν (actionEquiv F x) (actionEquiv F y)

theorem Intertwines.mul {F G : (Operators k A)ˣ}
    {μ ν ξ : Deformation.Binary (PowerSeries (LaurentSeries k)) (Vectors k A)}
    (hF : Intertwines F ν ξ) (hG : Intertwines G μ ν) :
    Intertwines (F * G) μ ξ := by
  intro x y
  simp only [actionEquiv_mul_apply]
  rw [hG x y, hF]

theorem Intertwines.inv {F : (Operators k A)ˣ}
    {μ ν : Deformation.Binary (PowerSeries (LaurentSeries k)) (Vectors k A)}
    (hF : Intertwines F μ ν) : Intertwines F⁻¹ ν μ := by
  intro x y
  simp only [actionEquiv_inv]
  apply (actionEquiv F).injective
  simp only [LinearEquiv.apply_symm_apply]
  rw [hF]
  simp only [LinearEquiv.apply_symm_apply]

/-- The actual operator is the product `J_M Φ J_L⁻¹`, in the ring of completed operators. -/
def conjugatedUnit (Φ J_L J_M : (Operators k A)ˣ) : (Operators k A)ˣ :=
  J_M * Φ * J_L⁻¹

@[simp] theorem conjugatedUnit_val (Φ J_L J_M : (Operators k A)ˣ) :
    (conjugatedUnit Φ J_L J_M : Operators k A) =
      (J_M : Operators k A) * (Φ : Operators k A) * (↑(J_L⁻¹) : Operators k A) := rfl

/-- No equation for the composed operator is assumed: it follows from the three factors. -/
theorem conjugatedUnit_intertwines (Φ J_L J_M : (Operators k A)ˣ)
    {μ_L μ_M σ_L σ_M : Deformation.Binary (PowerSeries (LaurentSeries k)) (Vectors k A)}
    (hΦ : Intertwines Φ μ_L μ_M)
    (hJ_L : Intertwines J_L μ_L σ_L) (hJ_M : Intertwines J_M μ_M σ_M) :
    Intertwines (conjugatedUnit Φ J_L J_M) σ_L σ_M :=
  (hJ_M.mul hΦ).mul hJ_L.inv

/-- The outer constant coefficient is the identity when both comparisons have the same
outer constant coefficient. That coefficient need not itself be the identity. -/
theorem conjugatedUnit_constantCoeff (Φ J_L J_M : (Operators k A)ˣ)
    (hΦ : PowerSeries.constantCoeff (Φ : Operators k A) = 1)
    (hJ : PowerSeries.constantCoeff (J_L : Operators k A) =
      PowerSeries.constantCoeff (J_M : Operators k A)) :
    PowerSeries.constantCoeff (conjugatedUnit Φ J_L J_M : Operators k A) = 1 := by
  rw [conjugatedUnit_val, map_mul, map_mul, hΦ, mul_one, ← hJ, ← map_mul,
    Units.mul_inv, map_one]

/-- The comparison is an element of the actual formal gauge group. -/
def conjugatedGauge (Φ J_L J_M : (Operators k A)ˣ)
    (hΦ : PowerSeries.constantCoeff (Φ : Operators k A) = 1)
    (hJ : PowerSeries.constantCoeff (J_L : Operators k A) =
      PowerSeries.constantCoeff (J_M : Operators k A)) :
    Deformation.Gauge.GaugeUnit (LaurentSeries (Module.End k A)) := by
  refine ⟨conjugatedUnit Φ J_L J_M, ?_⟩
  change toJet 1 (conjugatedUnit Φ J_L J_M : Operators k A) = 1
  rw [← map_one (toJet 1), toJet_eq_iff]
  intro n hn
  have hn0 : n = 0 := by omega
  subst n
  simpa only [PowerSeries.coeff_zero_eq_constantCoeff, map_one] using
    conjugatedUnit_constantCoeff Φ J_L J_M hΦ hJ

@[simp] theorem conjugatedGauge_series (Φ J_L J_M : (Operators k A)ˣ)
    (hΦ : PowerSeries.constantCoeff (Φ : Operators k A) = 1)
    (hJ : PowerSeries.constantCoeff (J_L : Operators k A) =
      PowerSeries.constantCoeff (J_M : Operators k A)) :
    (conjugatedGauge Φ J_L J_M hΦ hJ).series =
      (conjugatedUnit Φ J_L J_M : Operators k A) := rfl

end Assembly

section ActualComparison

variable {k ι L M : Type*} [Field k] [CharZero k] [Fintype ι] [LinearOrder ι]
    [LieRing L] [LieAlgebra k L] [LieRing M] [LieAlgebra k M]
    {bL : Module.Basis ι k L} {bM : Module.Basis ι k M}
    (dL : WeightData bL) (dM : WeightData bM)
    (Φ : UniversalEnvelopingAlgebra k L ≃ₐ[k] UniversalEnvelopingAlgebra k M)
    (hw : dL.weight = dM.weight)
    (hΦ : EnvelopingFamily.LeadingGenerators dL dM Φ.toAlgHom)
    (hΦ' : EnvelopingFamily.LeadingGenerators dM dL Φ.symm.toAlgHom)

/-- Substitute the actual E2/E3 comparison, whose uniform Laurent bound was proved. -/
def ofRees (J_L J_M : (Operators k (PolynomialCoefficientOperators.Coordinates ι k))ˣ) :
    (Operators k (PolynomialCoefficientOperators.Coordinates ι k))ˣ :=
  conjugatedUnit (UniformBound.completedUnit dL dM Φ hw hΦ hΦ') J_L J_M

theorem ofRees_constantCoeff
    (J_L J_M : (Operators k (PolynomialCoefficientOperators.Coordinates ι k))ˣ)
    (hJ : PowerSeries.constantCoeff (J_L : Operators k (PolynomialCoefficientOperators.Coordinates ι k)) =
      PowerSeries.constantCoeff (J_M : Operators k (PolynomialCoefficientOperators.Coordinates ι k))) :
    PowerSeries.constantCoeff (ofRees dL dM Φ hw hΦ hΦ' J_L J_M : Operators k (PolynomialCoefficientOperators.Coordinates ι k)) = 1 := by
  apply conjugatedUnit_constantCoeff _ _ _ _ hJ
  exact UniformBound.completedOperator_constantCoeff dL dM Φ hw hΦ hΦ'

/-- The actual E2/E3 unit, conjugated by the coherent comparisons, belongs to the
formal gauge subgroup rather than merely to an unrelated ambient automorphism group. -/
def ofReesGauge
    (J_L J_M : (Operators k (PolynomialCoefficientOperators.Coordinates ι k))ˣ)
    (hJ : PowerSeries.constantCoeff (J_L : Operators k (PolynomialCoefficientOperators.Coordinates ι k)) =
      PowerSeries.constantCoeff (J_M : Operators k (PolynomialCoefficientOperators.Coordinates ι k))) :
    Deformation.Gauge.GaugeUnit
      (LaurentSeries (Module.End k (PolynomialCoefficientOperators.Coordinates ι k))) :=
  conjugatedGauge (UniformBound.completedUnit dL dM Φ hw hΦ hΦ') J_L J_M
    (UniformBound.completedOperator_constantCoeff dL dM Φ hw hΦ hΦ') hJ

end ActualComparison

end EnvelopingIsomorphism.Rees.StarComparison
