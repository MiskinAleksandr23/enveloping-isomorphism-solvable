import EnvelopingIsomorphism.Deformation.Gauge.LaurentPathLift
import EnvelopingIsomorphism.Deformation.Gauge.LowTangent

/-! The genuine short Laurent Hochschild complex used by gauge reflection.
Every relevant arity retains all original coefficient cochains; degrees outside
-1, 0, 1, 2 are zero. We assert no quasi-isomorphism of this short complex with
a full complex. Reflection only consumes middle exactness of its explicit low
sequence, established separately from the actual tangent coefficients. -/

noncomputable section

set_option maxSynthPendingDepth 3

namespace EnvelopingIsomorphism.Deformation.Gauge.LaurentConjugation

open EnvelopingIsomorphism.FormalSeries PowerSeriesModule

universe u v
variable {k : Type u} [CommRing k] {A : Type v} [AddCommGroup A] [Module k A]

variable (μ : BinaryCoefficients (k := k) (A := A))
variable (hμ : ∀ a b c, evaluateCoefficient μ (evaluateCoefficient μ a b) c =
  evaluateCoefficient μ a (evaluateCoefficient μ b c))

include hμ in
theorem differentialUnary_innerCoefficient_zero (u : Functions (k := k) (A := A)) :
    differentialUnary μ (innerCoefficient μ u) = 0 := by
  apply LaurentModule.binaryEvaluation_injective
  change evaluateCoefficient _ = evaluateCoefficient 0
  rw [evaluate_differentialUnary, evaluate_innerCoefficient, map_zero]
  exact differentialOne_differentialZero (evaluateCoefficient μ) hμ u

include hμ in
theorem differentialBinary_differentialUnary_zero (X : OperatorCoefficients (k := k) (A := A)) :
    LaurentModule.differentialBinarySeries μ (differentialUnary μ X) = 0 := by
  apply LaurentModule.ternaryEvaluation_injective
  rw [LaurentModule.ternaryEvaluation_differentialBinarySeries, map_zero]
  change differentialTwo (evaluateCoefficient μ) (evaluateCoefficient (differentialUnary μ X)) = 0
  rw [evaluate_differentialUnary]
  exact differentialTwo_differentialOne (evaluateCoefficient μ) hμ (evaluateOperator X)

/-- Existing full coefficient modules in the four degrees used by reflection. -/
@[reducible] def targetObjects : ℤ → ModuleCat.{v} (Scalars (k := k))
  | Int.negSucc 0 => ModuleCat.of (Scalars (k := k)) (Functions (k := k) (A := A))
  | Int.ofNat 0 => ModuleCat.of (Scalars (k := k)) (OperatorCoefficients (k := k) (A := A))
  | Int.ofNat 1 => ModuleCat.of (Scalars (k := k)) (BinaryCoefficients (k := k) (A := A))
  | Int.ofNat 2 => ModuleCat.of (Scalars (k := k)) (LaurentModule k (Ternary k A))
  | _ => ModuleCat.of (Scalars (k := k)) PUnit

/-- The actual low Hochschild differentials, and zero elsewhere. -/
def targetD (p : ℤ) : targetObjects (k := k) (A := A) p →ₗ[Scalars (k := k)]
    targetObjects (k := k) (A := A) (p + 1) :=
  if h : p = -1 then by subst p; exact innerCoefficient μ
  else if h : p = 0 then by subst p; exact differentialUnary μ
  else if h : p = 1 then by subst p; exact LaurentModule.differentialBinarySeries μ
  else 0

@[simp] theorem targetD_negative_one : targetD μ (-1) = innerCoefficient μ := by
  simp [targetD]

@[simp] theorem targetD_zero : targetD μ 0 = differentialUnary μ := by
  simp only [targetD, show (0 : ℤ) ≠ -1 by decide, ↓reduceDIte]

@[simp] theorem targetD_one : targetD μ 1 = LaurentModule.differentialBinarySeries μ := by
  simp only [targetD, show (1 : ℤ) ≠ -1 by decide, show (1 : ℤ) ≠ 0 by decide, ↓reduceDIte]

theorem targetD_other (p : ℤ) (hm : p ≠ -1) (h0 : p ≠ 0) (h1 : p ≠ 1) : targetD μ p = 0 := by
  simp only [targetD, dif_neg hm, dif_neg h0, dif_neg h1]

include hμ in
theorem targetD_sq (p : ℤ) (x : targetObjects (k := k) (A := A) p) :
    targetD μ (p + 1) (targetD μ p x) = 0 := by
  by_cases hm : p = -1
  · subst p
    change targetD μ 0 (targetD μ (-1) x) = 0
    rw [targetD_zero, targetD_negative_one]
    exact differentialUnary_innerCoefficient_zero μ hμ x
  by_cases h0 : p = 0
  · subst p
    change targetD μ 1 (targetD μ 0 x) = 0
    rw [targetD_one, targetD_zero]
    exact differentialBinary_differentialUnary_zero μ hμ x
  by_cases h1 : p = 1
  · subst p
    change targetD μ 2 (targetD μ 1 x) = 0
    rw [targetD_other μ 2 (by decide) (by decide) (by decide)]
    rfl
  rw [targetD_other μ p hm h0 h1, LinearMap.zero_apply, map_zero]

/-- A standard CochainComplex with actual Laurent full-cochain low objects. -/
def targetComplex : CochainComplex (ModuleCat.{v} (Scalars (k := k))) ℤ :=
  CochainComplex.of (targetObjects (k := k) (A := A))
    (fun p ↦ ModuleCat.ofHom (targetD μ p)) (by
      intro p
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact targetD_sq μ hμ p x)

@[simp] theorem targetComplex_d (p : ℤ) :
    ((targetComplex μ hμ).d p (p + 1)).hom = targetD μ p := by
  simp only [targetComplex, CochainComplex.of_d]
  rfl

@[simp] theorem targetComplex_d_negative_one :
    ((targetComplex μ hμ).d (-1) 0).hom = innerCoefficient μ := by
  change ((targetComplex μ hμ).d (-1) (-1 + 1)).hom = _
  rw [targetComplex_d, targetD_negative_one]

@[simp] theorem targetComplex_d_zero :
    ((targetComplex μ hμ).d 0 1).hom = differentialUnary μ := by
  change ((targetComplex μ hμ).d 0 (0 + 1)).hom = _
  rw [targetComplex_d, targetD_zero]

@[simp] theorem targetComplex_d_one :
    ((targetComplex μ hμ).d 1 2).hom = LaurentModule.differentialBinarySeries μ := by
  change ((targetComplex μ hμ).d 1 (1 + 1)).hom = _
  rw [targetComplex_d, targetD_one]

/-- The actual signed insertion in degree one. -/
def targetQuadratic : (targetComplex μ hμ).X 1 →ₗ[Scalars (k := k)]
    (targetComplex μ hμ).X 1 →ₗ[Scalars (k := k)] (targetComplex μ hμ).X 2 :=
  LaurentModule.insertBinarySeries

theorem targetMC_eq :
    MCSeries ((targetComplex μ hμ).d 1 2).hom (targetQuadratic μ hμ) = MC μ := by
  rw [targetComplex_d_one]
  rfl


abbrev TargetMC := MCSeries ((targetComplex μ hμ).d 1 2).hom (targetQuadratic μ hμ)

/-- No cochain or MC carrier is replaced: the two concrete definitions agree. -/
def targetMCEquiv : TargetMC μ hμ ≃ MC μ := Equiv.refl _

@[simp] theorem targetMCEquiv_val (b : TargetMC μ hμ) : (targetMCEquiv μ hμ b).val = b.val := rfl

/-- The constructed raw Laurent action is the action on the standard target complex. -/
@[reducible] def targetMulAction :
    MulAction (GaugeUnit (OperatorRing (k := k) (A := A))) (TargetMC μ hμ) := mcMulAction μ hμ

/-- The raw coefficient ring is additively identical to the actual degree-zero object. -/
def targetCoordinates : OperatorRing (k := k) (A := A) ≃+ (targetComplex μ hμ).X 0 :=
  operatorCoordinates

section TargetAction

local instance : MulAction (GaugeUnit (OperatorRing (k := k) (A := A))) (TargetMC μ hμ) :=
  targetMulAction μ hμ

@[simp] theorem target_smul_eq (G : GaugeUnit (OperatorRing (k := k) (A := A))) (b : TargetMC μ hμ) :
    G • b = transport μ hμ G b := rfl

theorem target_smul_agree (G : GaugeUnit (OperatorRing (k := k) (A := A))) (b : TargetMC μ hμ)
    {N : ℕ} (hG : NearIdentity N G.series) : AgreeBelow N (G • b).val b.val :=
  transport_agree μ hμ G b hG

theorem target_smul_leading (N : ℕ) (hN : 0 < N)
    (G : GaugeUnit (OperatorRing (k := k) (A := A))) (hG : NearIdentity N G.series) (b : TargetMC μ hμ) :
    coeffV N (G • b).val - coeffV N b.val =
      -(targetComplex μ hμ).d 0 1 (targetCoordinates μ hμ (PowerSeries.coeff N G.series)) := by
  change _ = -((targetComplex μ hμ).d 0 1).hom _
  rw [targetComplex_d_zero]
  exact transport_leading μ hμ G b hN hG

section Rational

variable [Algebra ℚ k] [Module ℚ A]

/-- Actual boundary stabilizers in precisely the low-complex interface. -/
def targetBoundary (N : ℕ) (u : (targetComplex μ hμ).X (-1)) (b : TargetMC μ hμ) :
    GaugeUnit (OperatorRing (k := k) (A := A)) := mcBoundary μ N u b

theorem targetBoundary_near (N : ℕ) (u : (targetComplex μ hμ).X (-1)) (b : TargetMC μ hμ) :
    NearIdentity N (targetBoundary μ hμ N u b).series := mcBoundary_near μ N u b

theorem targetBoundary_leading (N : ℕ) (hN : 0 < N)
    (u : (targetComplex μ hμ).X (-1)) (b : TargetMC μ hμ) :
    targetCoordinates μ hμ (PowerSeries.coeff N (targetBoundary μ hμ N u b).series) =
      (targetComplex μ hμ).d (-1) 0 u := by
  change operatorCoordinates (PowerSeries.coeff N (mcBoundary μ N u b).series) =
    ((targetComplex μ hμ).d (-1) 0).hom u
  rw [targetComplex_d_negative_one]
  exact mcBoundary_leading_coordinates μ N hN u b

theorem targetBoundary_fixes (N : ℕ) (hN : 0 < N)
    (u : (targetComplex μ hμ).X (-1)) (b : TargetMC μ hμ) :
    targetBoundary μ hμ N u b • b = b := mcBoundary_fixes μ hμ N hN u b


/-- The raw ordered unit satisfies the exact target action and leading-coordinate interface. -/
theorem target_ordered_lift_spec
    {V : Type*} [AddCommGroup V] [Module (Scalars (k := k)) V]
    (T : TaylorFamily (k := Scalars (k := k)) (V := V) (W := (targetComplex μ hμ).X 1))
    (b : ModulePath (Scalars (k := k)) V)
    (start finish : PowerSeriesModule (Scalars (k := k)) V)
    (hb0 : PolynomialModuleCalculus.seriesEval 0 b = start)
    (hb1 : PolynomialModuleCalculus.seriesEval 1 b = finish)
    (initial final : TargetMC μ hμ) (hi : initial.val = taylorApply T start)
    (hf : final.val = taylorApply T finish)
    (X : PathOrderedExp.PathSeries (OperatorRing (k := k) (A := A))) (N : ℕ) (hN : 0 < N)
    (hX : ∀ i < N, PowerSeries.coeff i X = 0) (x : (targetComplex μ hμ).X 0)
    (hx : PowerSeries.coeff N X = Polynomial.C ((targetCoordinates μ hμ).symm x))
    (hProducer : pathMap evaluateCoefficient (polynomialTaylorDerivative T b) =
      pathOperator (orderedVelocity (PathOrderedExp.mapPath LaurentOperator.actionHom X))
        (pathMap evaluateCoefficient (quantizedPath T (single 0 μ) b))) :
    NearIdentity N (orderedGauge X).series ∧
      targetCoordinates μ hμ (PowerSeries.coeff N (orderedGauge X).series) = x ∧
        orderedGauge X • initial = final :=
  rawOrderedGauge_lift_spec μ hμ T b start finish hb0 hb1 initial final hi hf X N hN hX x hx hProducer

end Rational

end TargetAction

end EnvelopingIsomorphism.Deformation.Gauge.LaurentConjugation
