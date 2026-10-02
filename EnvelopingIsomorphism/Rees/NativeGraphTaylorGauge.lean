import EnvelopingIsomorphism.Rees.GraphTaylorIdentification
import EnvelopingIsomorphism.Rees.GeometricStarComparison
import EnvelopingIsomorphism.FormalSeries.PolynomialCochainCoordinates
import EnvelopingIsomorphism.Deformation.Gauge.LaurentMC

/-! Transfer the actual F11 gauge to native polynomial cochains through the
genuine monomial coordinate equivalence, retaining the formal identity mark. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

namespace EnvelopingIsomorphism.Rees.NativeGraphTaylorGauge

open FormalSeries Deformation.Gauge
open PolynomialCochainCoordinates
open scoped PolynomialCochainCoordinates CompletedOperator CompletedPBWProduct
open scoped Classical

variable {k L M : Type*} [Field k] [CharZero k] [Algebra ℝ k] {d : ℕ}
    [LieRing L] [LieAlgebra k L] [LieRing M] [LieAlgebra k M]
    {bL : Module.Basis (Fin d) k L} {bM : Module.Basis (Fin d) k M}
    (D : WeightData bL) (D' : WeightData bM)
    (s : (j : ℕ) → Finset (Deformation.KontsevichGraph (j + 2)))
    (w : (j : ℕ) → Deformation.KontsevichGraph (j + 2) → Polynomial (Polynomial k))

local instance nativeBinaryLaurentGroup : AddCommGroup
    (LaurentModule k (Deformation.Binary k (MvPolynomial (Fin d) k))) :=
  @HahnModule.instAddCommGroup ℤ k (Deformation.Binary k (MvPolynomial (Fin d) k))
    inferInstance inferInstance inferInstance

local instance nativeBinarySeriesGroup : AddCommGroup
    (CompletedBinary.Families k (MvPolynomial (Fin d) k)) :=
  @HahnModule.instAddCommGroup ℕ (LaurentSeries k)
    (LaurentModule k (Deformation.Binary k (MvPolynomial (Fin d) k)))
    inferInstance inferInstance inferInstance

/-- The same completed graph family, expressed as native polynomial binary cochains. -/
def nativeFamily : CompletedBinary.Families k (MvPolynomial (Fin d) k) :=
  Transport.familyEquiv (coordinateEquiv (k := k) (d := d)).symm
    (GeometricStarComparison.graphFamily s w D)

variable
    (Φ : UniversalEnvelopingAlgebra k L ≃ₐ[k] UniversalEnvelopingAlgebra k M)
    (hw : D.weight = D'.weight)
    (hΦ : EnvelopingFamily.LeadingGenerators D D' Φ.toAlgHom)
    (hΦ' : EnvelopingFamily.LeadingGenerators D' D Φ.symm.toAlgHom)

/-- The actual F11 gauge is transported coefficientwise by conjugation of endomorphisms. -/
def gauge : GaugeUnit (LaurentSeries (Module.End k (MvPolynomial (Fin d) k))) := by
  let G := GeometricStarComparison.gauge s w D D' Φ hw hΦ hΦ'
  refine ⟨Transport.unitMap (coordinateEquiv (k := k) (d := d)).symm G.val, ?_⟩
  exact Transport.nearIdentity_operatorEquiv (coordinateEquiv (k := k) (d := d)).symm G.near_one

theorem gauge_conjugates (lawsL : GeometricStarComparison.ProductLaws s w D)
    (lawsM : GeometricStarComparison.ProductLaws s w D') :
    LaurentConjugation.conjugateFamily (gauge D D' s w Φ hw hΦ hΦ').val
        (nativeFamily D s w) = nativeFamily D' s w := by
  have h := congrArg (Transport.familyEquiv (coordinateEquiv (k := k) (d := d)).symm)
    (GeometricStarComparison.gauge_conjugates s w D D' Φ hw hΦ hΦ' lawsL lawsM)
  rw [Transport.familyEquiv_conjugateFamily] at h
  exact h

@[simp] theorem gauge_constantCoeff :
    PowerSeries.constantCoeff (gauge D D' s w Φ hw hΦ hΦ').series = 1 :=
  GaugeUnit.constantCoeff_series (R := LaurentSeries (Module.End k (MvPolynomial (Fin d) k))) _

section ScalarWeights

variable (w₀ : (j : ℕ) → Deformation.KontsevichGraph (j + 2) → k)

/-- The effective higher weights are inserted as constants in both parameters. -/
def parameterHigher (j : ℕ) (Γ : Deformation.KontsevichGraph (j + 2)) : Polynomial (Polynomial k) :=
  Polynomial.C (Polynomial.C (w₀ j Γ))

omit [CharZero k] in
theorem parameterFirstWeights :
    Deformation.KontsevichGraph.geometricFirstWeights (parameterHigher w₀) =
      GraphTaylorIdentification.parameterWeights
        (Deformation.KontsevichGraph.geometricFirstWeights w₀) := by
  funext j Γ
  cases j with
  | zero =>
    change algebraMap ℝ (Polynomial (Polynomial k)) _ = Polynomial.C (Polynomial.C (algebraMap ℝ k _))
    simp only [Polynomial.algebraMap_apply]
  | succ j => rfl

omit [CharZero k] in
/-- The inverse coordinate transport agrees with the actual native family used
in the proved Taylor identification. -/
theorem nativeFamily_parameters :
    nativeFamily D s (parameterHigher w₀) =
      GraphTaylorIdentification.nativeGraphFamily D
        (Deformation.KontsevichGraph.geometricFirstSets s)
        (Deformation.KontsevichGraph.geometricFirstWeights w₀) := by
  unfold nativeFamily GeometricStarComparison.graphFamily
  rw [parameterFirstWeights, ← Transport.familyEquiv_symm_apply]
  change familyCoordinates.symm
    (GraphTaylorIdentification.graphFamily D
      (Deformation.KontsevichGraph.geometricFirstSets s)
      (Deformation.KontsevichGraph.geometricFirstWeights w₀)) = _
  rw [familyCoordinates_symm_apply]
  rfl

/-- The actual native gauge conjugates the actual full Taylor evaluations,
with all coordinate changes and graph-product identifications proved. -/
theorem gauge_conjugates_fullTaylor
    (lawsL : GeometricStarComparison.ProductLaws s (parameterHigher w₀) D)
    (lawsM : GeometricStarComparison.ProductLaws s (parameterHigher w₀) D') :
    LaurentConjugation.conjugateFamily
        (gauge D D' s (parameterHigher w₀) Φ hw hΦ hΦ').val
        (GraphTaylorIdentification.fullTaylor D
          (Deformation.KontsevichGraph.geometricFirstSets s)
          (Deformation.KontsevichGraph.geometricFirstWeights w₀)) =
      GraphTaylorIdentification.fullTaylor D'
        (Deformation.KontsevichGraph.geometricFirstSets s)
        (Deformation.KontsevichGraph.geometricFirstWeights w₀) := by
  rw [GraphTaylorIdentification.fullTaylor_eq_nativeGraphFamily,
    GraphTaylorIdentification.fullTaylor_eq_nativeGraphFamily,
    ← nativeFamily_parameters, ← nativeFamily_parameters]
  exact gauge_conjugates D D' s (parameterHigher w₀) Φ hw hΦ hΦ' lawsL lawsM

omit [CharZero k] in
/-- The common native zero-fiber bivector gives the same full Laurent base product. -/
theorem fullTaylor_base_eq
    (hbase : PoissonMCFamily.constantBivector D = PoissonMCFamily.constantBivector D') :
    PowerSeriesModule.coeffV 0
        (GraphTaylorIdentification.fullTaylor D
          (Deformation.KontsevichGraph.geometricFirstSets s)
          (Deformation.KontsevichGraph.geometricFirstWeights w₀)) =
      PowerSeriesModule.coeffV 0
        (GraphTaylorIdentification.fullTaylor D'
          (Deformation.KontsevichGraph.geometricFirstSets s)
          (Deformation.KontsevichGraph.geometricFirstWeights w₀)) := by
  apply LaurentModule.ext
  intro j
  cases j with
  | ofNat n =>
    simp only [Int.ofNat_eq_natCast]
    rw [GraphTaylorIdentification.fullTaylor, GraphTaylorIdentification.fullTaylor,
      coeff_laurentScaledMCEvaluation_nat, coeff_laurentScaledMCEvaluation_nat,
      PowerSeriesModule.coeffV_applyMultilinear, PowerSeriesModule.coeffV_applyMultilinear]
    simp only [Finset.piAntidiag_zero, Finset.sum_singleton, Pi.zero_apply,
      PoissonMCFamily.poissonSeries_coeff]
    change GraphTaylorCoefficients.effectiveFamily _ _ n (fun _ ↦ PoissonMCFamily.constantBivector D) =
      GraphTaylorCoefficients.effectiveFamily _ _ n (fun _ ↦ PoissonMCFamily.constantBivector D')
    rw [hbase]
  | negSucc n =>
    rw [GraphTaylorIdentification.fullTaylor, GraphTaylorIdentification.fullTaylor,
      coeff_laurentScaledMCEvaluation_neg _ _ _ _ (Int.negSucc_lt_zero n),
      coeff_laurentScaledMCEvaluation_neg _ _ _ _ (Int.negSucc_lt_zero n)]

/-- The actual native F11 gauge transports the two actual twisted Taylor outputs.
The source of both Taylor evaluations is twisted at the same proved base bivector. -/
theorem gauge_transports_taylor
    (lawsL : GeometricStarComparison.ProductLaws s (parameterHigher w₀) D)
    (lawsM : GeometricStarComparison.ProductLaws s (parameterHigher w₀) D') :
    LaurentConjugation.transportFamily
        (PowerSeriesModule.coeffV 0
          (GraphTaylorIdentification.fullTaylor D
            (Deformation.KontsevichGraph.geometricFirstSets s)
            (Deformation.KontsevichGraph.geometricFirstWeights w₀)))
        (gauge D D' s (parameterHigher w₀) Φ hw hΦ hΦ')
        (taylorApply
          (laurentPlacementTaylorFamily
            (GraphTaylorCoefficients.effectiveFamily
              (Deformation.KontsevichGraph.geometricFirstSets s)
              (Deformation.KontsevichGraph.geometricFirstWeights w₀))
            (PoissonMCFamily.constantBivector D))
          (PoissonMCFamily.perturbationSeries D)) =
      taylorApply
        (laurentPlacementTaylorFamily
          (GraphTaylorCoefficients.effectiveFamily
            (Deformation.KontsevichGraph.geometricFirstSets s)
            (Deformation.KontsevichGraph.geometricFirstWeights w₀))
          (PoissonMCFamily.constantBivector D))
        (PoissonMCFamily.perturbationSeries D') := by
  have hbase := PoissonMCFamily.constantBivector_eq_of_zero D D'
    (GraphStarComparison.zero_coeff_eq D D' Φ hw hΦ hΦ')
  have hL := GraphTaylorIdentification.taylorApply_eq_graph_difference D
    (Deformation.KontsevichGraph.geometricFirstSets s)
    (Deformation.KontsevichGraph.geometricFirstWeights w₀)
  have hM := GraphTaylorIdentification.taylorApply_eq_graph_difference D'
    (Deformation.KontsevichGraph.geometricFirstSets s)
    (Deformation.KontsevichGraph.geometricFirstWeights w₀)
  rw [← hbase] at hM
  rw [hL, hM, ← GraphTaylorIdentification.fullTaylor_eq_nativeGraphFamily,
    ← GraphTaylorIdentification.fullTaylor_eq_nativeGraphFamily,
    LaurentConjugation.transportFamily]
  rw [← add_sub_assoc, add_sub_cancel_left,
    gauge_conjugates_fullTaylor D D' s Φ hw hΦ hΦ' w₀ lawsL lawsM,
    fullTaylor_base_eq D D' s w₀ hbase]

end ScalarWeights

end EnvelopingIsomorphism.Rees.NativeGraphTaylorGauge
