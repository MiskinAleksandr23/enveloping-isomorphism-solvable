import EnvelopingIsomorphism.Deformation.Gauge.LaurentMC
import EnvelopingIsomorphism.Deformation.Gauge.BoundaryPath
import EnvelopingIsomorphism.FormalSeries.PathOrderedNaturality

/-! The full inner boundary generator remains a Laurent series of original
coefficient endomorphisms. Its path-ordered unit acts on genuine Laurent-valued
function series through the established ring homomorphism. -/

noncomputable section

set_option maxSynthPendingDepth 3

namespace EnvelopingIsomorphism.Deformation.Gauge.LaurentConjugation

open EnvelopingIsomorphism.FormalSeries PowerSeriesModule

universe u v
variable {k : Type u} [CommRing k] {A : Type v} [AddCommGroup A] [Module k A]

/-- Contract the full Laurent binary cochain with a Laurent constant cochain. -/
def innerCoefficient : BinaryCoefficients (k := k) (A := A) →ₗ[Scalars (k := k)]
    Functions (k := k) (A := A) →ₗ[Scalars (k := k)] OperatorCoefficients (k := k) (A := A) :=
  LaurentModule.linearApply - (LaurentModule.linearApply (k := k) (V := A) (W := Unary k A)).comp
    LaurentModule.flipBinarySeries

theorem innerCoefficient_apply (B : BinaryCoefficients (k := k) (A := A))
    (u : Functions (k := k) (A := A)) : innerCoefficient B u =
      LaurentModule.linearApply B u - LaurentModule.linearApply (LaurentModule.flipBinarySeries B) u := rfl

theorem evaluate_innerCoefficient (B : BinaryCoefficients (k := k) (A := A))
    (u : Functions (k := k) (A := A)) :
    evaluateOperator (innerCoefficient B u) = differentialZero (evaluateCoefficient B) u := by
  rw [innerCoefficient_apply, map_sub]
  apply LinearMap.ext
  intro v
  change LaurentModule.extendBinary B u v -
    LaurentModule.extendBinary (LaurentModule.flipBinarySeries B) u v =
      LaurentModule.extendBinary B u v - LaurentModule.extendBinary B v u
  rw [← LaurentModule.extendBinary_flip]

theorem boundedBelow_innerCoefficient (B : BinaryCoefficients (k := k) (A := A))
    (u : Functions (k := k) (A := A)) {b c : ℤ}
    (hB : LaurentModule.BoundedBelow b B) (hu : LaurentModule.BoundedBelow c u) :
    LaurentModule.BoundedBelow (b + c) (innerCoefficient B u) := by
  rw [innerCoefficient_apply]
  have hflip : LaurentModule.BoundedBelow b (LaurentModule.flipBinarySeries B) :=
    LaurentModule.boundedBelow_map _ hB
  intro d hd
  rw [LaurentModule.coeff_sub, LaurentModule.boundedBelow_linearApply B u hB hu d hd,
    LaurentModule.boundedBelow_linearApply _ u hflip hu d hd, sub_self]

/-- The full deformed inner operator, with one independent Laurent bound in each t-degree. -/
def rawInnerSeries (B : Families (k := k) (A := A)) (u : Functions (k := k) (A := A)) :
    PowerSeries (OperatorRing (k := k) (A := A)) :=
  PowerSeries.mk fun n ↦ operatorCoordinates.symm (innerCoefficient (coeffV n B) u)

@[simp] theorem coeff_rawInnerSeries (B : Families (k := k) (A := A))
    (u : Functions (k := k) (A := A)) (n : ℕ) :
    PowerSeries.coeff n (rawInnerSeries B u) =
      operatorCoordinates.symm (innerCoefficient (coeffV n B) u) := by
  exact PowerSeries.coeff_mk _ _

theorem ambientOperators_rawInnerSeries (B : Families (k := k) (A := A))
    (u : Functions (k := k) (A := A)) :
    ambientOperators (rawInnerSeries B u) = Gauge.innerSeries (embed B) u := by
  apply PowerSeries.ext
  intro n
  change LaurentOperator.actionHom (PowerSeries.coeff n (rawInnerSeries B u)) = _
  rw [coeff_rawInnerSeries]
  rw [← evaluateOperator_coordinates, AddEquiv.apply_symm_apply, evaluate_innerCoefficient,
    Gauge.coeff_innerSeries]
  rfl

def rawBoundaryVelocity (N : ℕ) (B : Families (k := k) (A := A))
    (u : Functions (k := k) (A := A)) : PowerSeries (OperatorRing (k := k) (A := A)) :=
  PowerSeries.X ^ N * rawInnerSeries B u

theorem rawBoundaryVelocity_coeff_below (N : ℕ) (B : Families (k := k) (A := A))
    (u : Functions (k := k) (A := A)) (i : ℕ) (hi : i < N) :
    PowerSeries.coeff i (rawBoundaryVelocity N B u) = 0 := by
  simp [rawBoundaryVelocity, PowerSeries.coeff_X_pow_mul', Nat.not_le.mpr hi]

@[simp] theorem rawBoundaryVelocity_leading (N : ℕ) (B : Families (k := k) (A := A))
    (u : Functions (k := k) (A := A)) :
    PowerSeries.coeff N (rawBoundaryVelocity N B u) =
      operatorCoordinates.symm (innerCoefficient (coeffV 0 B) u) := by
  simp [rawBoundaryVelocity, PowerSeries.coeff_X_pow_mul']

theorem ambientOperators_rawBoundaryVelocity (N : ℕ) (B : Families (k := k) (A := A))
    (u : Functions (k := k) (A := A)) :
    ambientOperators (rawBoundaryVelocity N B u) = Gauge.boundaryVelocity N (embed B) u := by
  rw [rawBoundaryVelocity, map_mul, map_pow, ambientOperators_rawInnerSeries]
  change PowerSeries.map _ PowerSeries.X ^ N * _ = _
  rw [PowerSeries.map_X]
  rfl

/-- Constant in the auxiliary path parameter, retaining the entire deformed inner series. -/
def rawBoundaryPath (N : ℕ) (B : Families (k := k) (A := A))
    (u : Functions (k := k) (A := A)) : PathOrderedExp.PathSeries (OperatorRing (k := k) (A := A)) :=
  PowerSeries.map Polynomial.C (rawBoundaryVelocity N B u)

theorem rawBoundaryPath_coeff_below (N : ℕ) (B : Families (k := k) (A := A))
    (u : Functions (k := k) (A := A)) (i : ℕ) (hi : i < N) :
    PowerSeries.coeff i (rawBoundaryPath N B u) = 0 := by
  simp only [rawBoundaryPath, PowerSeries.coeff_map, rawBoundaryVelocity_coeff_below N B u i hi, map_zero]

@[simp] theorem rawBoundaryPath_leading (N : ℕ) (B : Families (k := k) (A := A))
    (u : Functions (k := k) (A := A)) :
    PowerSeries.coeff N (rawBoundaryPath N B u) =
      Polynomial.C (operatorCoordinates.symm (innerCoefficient (coeffV 0 B) u)) := by
  simp only [rawBoundaryPath, PowerSeries.coeff_map, rawBoundaryVelocity_leading]

theorem mapPath_rawBoundaryPath (N : ℕ) (B : Families (k := k) (A := A))
    (u : Functions (k := k) (A := A)) :
    PathOrderedExp.mapPath LaurentOperator.actionHom (rawBoundaryPath N B u) =
      PowerSeries.map Polynomial.C (Gauge.boundaryVelocity N (embed B) u) := by
  rw [← ambientOperators_rawBoundaryVelocity]
  ext n
  simp only [PathOrderedExp.coeff_mapPath, rawBoundaryPath, PowerSeries.coeff_map,
    Polynomial.map_C]
  rfl

section Rational

variable [Algebra ℚ k]

/-- Restriction of the existing E-module structure along the canonical rational scalars. -/
scoped instance rationalFunctionsModule : Module ℚ (Functions (k := k) (A := A)) :=
  Module.compHom (Functions (k := k) (A := A)) (algebraMap ℚ (Scalars (k := k)))

variable [Module ℚ A]

/-- The actual raw Laurent-operator unit integrating the full inner boundary. -/
def boundaryGauge (N : ℕ) (B : Families (k := k) (A := A)) (u : Functions (k := k) (A := A)) :
    GaugeUnit (OperatorRing (k := k) (A := A)) := orderedGauge (rawBoundaryPath N B u)

theorem boundaryGauge_near (N : ℕ) (B : Families (k := k) (A := A))
    (u : Functions (k := k) (A := A)) : NearIdentity N (boundaryGauge N B u).series :=
  orderedGauge_near _ N (rawBoundaryPath_coeff_below N B u)

theorem boundaryGauge_leading (N : ℕ) (hN : 0 < N) (B : Families (k := k) (A := A))
    (u : Functions (k := k) (A := A)) :
    PowerSeries.coeff N (boundaryGauge N B u).series =
      operatorCoordinates.symm (innerCoefficient (coeffV 0 B) u) :=
  orderedGauge_leading _ N hN (rawBoundaryPath_coeff_below N B u) _ (rawBoundaryPath_leading N B u)

theorem ambientGauge_boundaryGauge (N : ℕ) (B : Families (k := k) (A := A))
    (u : Functions (k := k) (A := A)) :
    ambientGauge (boundaryGauge N B u) =
      Gauge.boundaryPathGauge N (embed B) u := by
  apply Subtype.ext
  change Units.map (PowerSeries.map LaurentOperator.actionHom).toMonoidHom
    (PathOrderedExp.endpointUnit (rawBoundaryPath N B u)) = _
  rw [← PathOrderedExp.endpointUnit_mapPath, mapPath_rawBoundaryPath]
  rfl

/-- The constructed raw Laurent unit fixes the entire associative family. -/
theorem boundaryGauge_fixes (N : ℕ) (hN : 0 < N) (B : Families (k := k) (A := A))
    (u : Functions (k := k) (A := A))
    (hB : ∀ x y z, evaluateFamily B (evaluateFamily B x y) z =
      evaluateFamily B x (evaluateFamily B y z)) :
    conjugateFamily (boundaryGauge N B u).val B = B := by
  apply embed_injective
  rw [embed_conjugateFamily]
  change conjugateBinarySeries (ambientGauge (boundaryGauge N B u)).val (embed B) = embed B
  rw [ambientGauge_boundaryGauge]
  exact Gauge.boundaryPathGauge_fixes N hN (embed B) u hB

/-- Boundary stabilizer in actual coefficient Maurer--Cartan coordinates. -/
def mcBoundary (μ : BinaryCoefficients (k := k) (A := A)) (N : ℕ)
    (u : Functions (k := k) (A := A)) (b : MC μ) :
    GaugeUnit (OperatorRing (k := k) (A := A)) :=
  boundaryGauge N (single 0 μ + b.val) u

theorem mcBoundary_near (μ : BinaryCoefficients (k := k) (A := A)) (N : ℕ)
    (u : Functions (k := k) (A := A)) (b : MC μ) :
    NearIdentity N (mcBoundary μ N u b).series := boundaryGauge_near N _ u

theorem mcBoundary_leading (μ : BinaryCoefficients (k := k) (A := A))
    (N : ℕ) (hN : 0 < N) (u : Functions (k := k) (A := A)) (b : MC μ) :
    PowerSeries.coeff N (mcBoundary μ N u b).series =
      operatorCoordinates.symm (innerCoefficient μ u) := by
  rw [mcBoundary, boundaryGauge_leading N hN]
  simp [b.property.1]

theorem mcBoundary_leading_coordinates (μ : BinaryCoefficients (k := k) (A := A))
    (N : ℕ) (hN : 0 < N) (u : Functions (k := k) (A := A)) (b : MC μ) :
    operatorCoordinates (PowerSeries.coeff N (mcBoundary μ N u b).series) = innerCoefficient μ u := by
  rw [mcBoundary_leading μ N hN, AddEquiv.apply_symm_apply]

theorem mcBoundary_fixes (μ : BinaryCoefficients (k := k) (A := A))
    (hμ : ∀ a b c, evaluateCoefficient μ (evaluateCoefficient μ a b) c =
      evaluateCoefficient μ a (evaluateCoefficient μ b c))
    (N : ℕ) (hN : 0 < N) (u : Functions (k := k) (A := A)) (b : MC μ) :
    transport μ hμ (mcBoundary μ N u b) b = b := by
  apply Subtype.ext
  rw [transport_val, transportFamily, mcBoundary,
    boundaryGauge_fixes N hN _ u ((mc_iff_associative μ hμ b.val).mp b.property.2)]
  abel

/-- Elementary raw Laurent corrections have the exact required degree-zero tangent. -/
theorem elementary_transport_leading (μ : BinaryCoefficients (k := k) (A := A))
    (hμ : ∀ a b c, evaluateCoefficient μ (evaluateCoefficient μ a b) c =
      evaluateCoefficient μ a (evaluateCoefficient μ b c))
    (N : ℕ) (hN : 0 < N) (X : OperatorCoefficients (k := k) (A := A)) (b : MC μ) :
    coeffV N (transport μ hμ (elementaryGauge N hN (operatorCoordinates.symm X)) b).val - coeffV N b.val =
      -differentialUnary μ X := by
  rw [transport_leading μ hμ _ b hN (elementaryGauge_near N hN _),
    elementaryGauge_leading, AddEquiv.apply_symm_apply]

end Rational

end EnvelopingIsomorphism.Deformation.Gauge.LaurentConjugation
