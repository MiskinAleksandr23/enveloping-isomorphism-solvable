import EnvelopingIsomorphism.Deformation.Gauge.LaurentPathLift
import EnvelopingIsomorphism.Deformation.Gauge.TangentPath

/-! Convert actual Laurent-coefficient tangent paths into raw noncommutative
operator paths. Only additive coordinate equivalences are used: the raw Laurent
endomorphism ring is not assigned a Laurent-scalar algebra structure.
-/

noncomputable section

set_option maxSynthPendingDepth 3

namespace EnvelopingIsomorphism.Deformation.Gauge.LaurentConjugation

open EnvelopingIsomorphism.FormalSeries PowerSeriesModule

universe u v w z
variable {k : Type u} [CommRing k]
variable {A : Type v} [AddCommGroup A] [Module k A]

/-- Finite polynomial coefficients transferred additively into the native operator ring. -/
def rawPolynomialEquiv :
    PolynomialModule (Scalars (k := k)) (OperatorCoefficients (k := k) (A := A)) ≃+
      Polynomial (OperatorRing (k := k) (A := A)) :=
  PolynomialModule.coeffAddEquiv.trans <|
    (Finsupp.mapRange.addEquiv operatorCoordinates.symm).trans <|
      AddMonoidAlgebra.coeffAddEquiv.symm.trans (Polynomial.toFinsuppIso _).symm.toAddEquiv

@[simp] theorem coeff_rawPolynomialEquiv
    (p : PolynomialModule (Scalars (k := k)) (OperatorCoefficients (k := k) (A := A))) (j : ℕ) :
    (rawPolynomialEquiv p).coeff j = operatorCoordinates.symm (p.coeff j) := rfl

@[simp] theorem rawPolynomialEquiv_single (j : ℕ) (a : OperatorCoefficients (k := k) (A := A)) :
    rawPolynomialEquiv (PolynomialModule.single (Scalars (k := k)) j a) =
      Polynomial.monomial j (operatorCoordinates.symm a) := by
  classical
  apply Polynomial.ext
  intro l
  simp only [coeff_rawPolynomialEquiv, PolynomialModule.coeff_single,
    Finsupp.single_apply, Polynomial.coeff_monomial]
  split_ifs <;> simp_all

/-- Outer complete paths retain all finite polynomial coefficients and Laurent supports. -/
def rawPathEquiv : ModulePath (Scalars (k := k)) (OperatorCoefficients (k := k) (A := A)) ≃+
    PathOrderedExp.PathSeries (OperatorRing (k := k) (A := A)) where
  toFun p := PowerSeries.mk (fun n ↦ rawPolynomialEquiv (coeffV n p))
  invFun p := PowerSeriesModule.mk (fun n ↦ rawPolynomialEquiv.symm (PowerSeries.coeff n p))
  left_inv p := by apply PowerSeriesModule.ext; intro n; simp
  right_inv p := by apply PowerSeries.ext; intro n; simp
  map_add' p q := by apply PowerSeries.ext; intro n; simp

@[simp] theorem coeff_rawPathEquiv
    (p : ModulePath (Scalars (k := k)) (OperatorCoefficients (k := k) (A := A))) (n : ℕ) :
    PowerSeries.coeff n (rawPathEquiv p) = rawPolynomialEquiv (coeffV n p) := by
  simp [rawPathEquiv]

theorem rawPathEquiv_preserves_order
    (p : ModulePath (Scalars (k := k)) (OperatorCoefficients (k := k) (A := A))) (N : ℕ)
    (hp : ∀ i < N, coeffV i p = 0) : ∀ i < N, PowerSeries.coeff i (rawPathEquiv p) = 0 := by
  intro i hi
  simp [hp i hi]

/-- The actual represented path is precisely coefficientwise evaluation of the module path. -/
theorem represented_rawPathEquiv
    (p : ModulePath (Scalars (k := k)) (OperatorCoefficients (k := k) (A := A))) :
    PolynomialModuleRingBridge.ofRingPath (k := Scalars (k := k))
      (PathOrderedExp.mapPath LaurentOperator.actionHom (rawPathEquiv p)) =
        pathMap evaluateOperator p := by
  apply PowerSeriesModule.ext
  intro n
  apply PolynomialModule.ext
  apply Finsupp.ext
  intro j
  simp only [PolynomialModuleRingBridge.ofRingPath, LinearEquiv.coe_toLinearMap,
    PolynomialModuleRingBridge.coeff_pathEquiv, PolynomialModuleRingBridge.coeff_toModule,
    PathOrderedExp.coeff_mapPath, Polynomial.coeff_map, pathMap, coeffV_map]
  change LaurentOperator.actionHom ((PowerSeries.coeff n (rawPathEquiv p)).coeff j) =
    evaluateOperator ((coeffV n p).coeff j)
  rw [coeff_rawPathEquiv, coeff_rawPolynomialEquiv,
    ← evaluateOperator_coordinates, AddEquiv.apply_symm_apply]

/-- Ordered conjugation velocity acts on binary cochains, after evaluating the underlying operators. -/
theorem orderedVelocity_rawPathEquiv
    (p : ModulePath (Scalars (k := k)) (OperatorCoefficients (k := k) (A := A))) :
    orderedVelocity (PathOrderedExp.mapPath LaurentOperator.actionHom (rawPathEquiv p)) =
      unaryVelocityPath (pathMap evaluateOperator p) := by
  unfold orderedVelocity
  rw [show PolynomialModuleRingBridge.pathEquiv
      (PathOrderedExp.mapPath LaurentOperator.actionHom (rawPathEquiv p)) =
        pathMap evaluateOperator p from represented_rawPathEquiv p]

theorem orderedVelocity_rawPathEquiv_comp
    (p : ModulePath (Scalars (k := k)) (OperatorCoefficients (k := k) (A := A))) :
    orderedVelocity (PathOrderedExp.mapPath LaurentOperator.actionHom (rawPathEquiv p)) =
      pathMap ((unaryActionLinear (k := Scalars (k := k)) (V := Functions (k := k) (A := A))).comp
        evaluateOperator) p := by
  rw [orderedVelocity_rawPathEquiv]
  apply PowerSeriesModule.ext
  intro n
  apply PolynomialModule.ext
  apply Finsupp.ext
  intro j
  rfl

variable {V₀ : Type w} [AddCommGroup V₀] [Module (Scalars (k := k)) V₀]
variable {V₁ : Type z} [AddCommGroup V₁] [Module (Scalars (k := k)) V₁]

/-- A genuine constant polynomial direction placed at outer order N. -/
def shiftedDirectionPath (N : ℕ) (y : V₀) : ModulePath (Scalars (k := k)) V₀ :=
  single N (PolynomialModule.single (Scalars (k := k)) 0 y)

theorem shiftedDirectionPath_coeff_below (N : ℕ) (y : V₀) :
    ∀ i < N, coeffV i (shiftedDirectionPath (k := k) N y) = 0 := by
  intro i hi
  simp [shiftedDirectionPath, Nat.ne_of_lt hi]

@[simp] theorem shiftedDirectionPath_leading (N : ℕ) (y : V₀) :
    coeffV N (shiftedDirectionPath (k := k) N y) = PolynomialModule.single (Scalars (k := k)) 0 y := by
  simp [shiftedDirectionPath]

/-- The raw operator velocity is produced from the actual polynomial tangent evaluation. -/
def rawVelocity
    (Q : TangentFamily (k := Scalars (k := k)) (V₀ := V₀) (V₁ := V₁)
      (W₀ := OperatorCoefficients (k := k) (A := A)))
    (P : ModulePath (Scalars (k := k)) V₁) (N : ℕ) (y : V₀) :
    PathOrderedExp.PathSeries (OperatorRing (k := k) (A := A)) :=
  rawPathEquiv (polynomialTangentApply Q P (shiftedDirectionPath N y))

theorem rawVelocity_coeff_below
    (Q : TangentFamily (k := Scalars (k := k)) (V₀ := V₀) (V₁ := V₁)
      (W₀ := OperatorCoefficients (k := k) (A := A)))
    (P : ModulePath (Scalars (k := k)) V₁) (N : ℕ) (y : V₀) :
    ∀ i < N, PowerSeries.coeff i (rawVelocity Q P N y) = 0 :=
  rawPathEquiv_preserves_order _ N
    (polynomialTangentApply_preserves_order Q P _ N (shiftedDirectionPath_coeff_below N y))

@[simp] theorem rawVelocity_leading
    (Q : TangentFamily (k := Scalars (k := k)) (V₀ := V₀) (V₁ := V₁)
      (W₀ := OperatorCoefficients (k := k) (A := A)))
    (P : ModulePath (Scalars (k := k)) V₁) (N : ℕ) (y : V₀) :
    PowerSeries.coeff N (rawVelocity Q P N y) = Polynomial.C (operatorCoordinates.symm (Q.linear y)) := by
  rw [rawVelocity, coeff_rawPathEquiv,
    polynomialTangentApply_leading_constant Q P _ N (shiftedDirectionPath_coeff_below N y) y
      (shiftedDirectionPath_leading N y), rawPolynomialEquiv_single, Polynomial.monomial_zero_left]

theorem rawVelocity_positive
    (Q : TangentFamily (k := Scalars (k := k)) (V₀ := V₀) (V₁ := V₁)
      (W₀ := OperatorCoefficients (k := k) (A := A)))
    (P : ModulePath (Scalars (k := k)) V₁) (N : ℕ) (hN : 0 < N) (y : V₀) :
    PowerSeries.constantCoeff (rawVelocity Q P N y) = 0 := by
  simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using rawVelocity_coeff_below Q P N y 0 hN

theorem represented_rawVelocity
    (Q : TangentFamily (k := Scalars (k := k)) (V₀ := V₀) (V₁ := V₁)
      (W₀ := OperatorCoefficients (k := k) (A := A)))
    (P : ModulePath (Scalars (k := k)) V₁) (N : ℕ) (y : V₀) :
    PolynomialModuleRingBridge.ofRingPath (k := Scalars (k := k))
      (PathOrderedExp.mapPath LaurentOperator.actionHom (rawVelocity Q P N y)) =
        pathMap evaluateOperator (polynomialTangentApply Q P (shiftedDirectionPath N y)) :=
  represented_rawPathEquiv _

theorem orderedVelocity_rawVelocity
    (Q : TangentFamily (k := Scalars (k := k)) (V₀ := V₀) (V₁ := V₁)
      (W₀ := OperatorCoefficients (k := k) (A := A)))
    (P : ModulePath (Scalars (k := k)) V₁) (N : ℕ) (y : V₀) :
    orderedVelocity (PathOrderedExp.mapPath LaurentOperator.actionHom (rawVelocity Q P N y)) =
      unaryVelocityPath (pathMap evaluateOperator
        (polynomialTangentApply Q P (shiftedDirectionPath N y))) :=
  orderedVelocity_rawPathEquiv _

section OrderedGauge

variable [Algebra ℚ k] [Module ℚ A]

/-- The actual path-ordered raw Laurent gauge associated with the computed velocity. -/
def rawVelocityGauge
    (Q : TangentFamily (k := Scalars (k := k)) (V₀ := V₀) (V₁ := V₁)
      (W₀ := OperatorCoefficients (k := k) (A := A)))
    (P : ModulePath (Scalars (k := k)) V₁) (N : ℕ) (y : V₀) :
    GaugeUnit (OperatorRing (k := k) (A := A)) := orderedGauge (rawVelocity Q P N y)

theorem rawVelocityGauge_near
    (Q : TangentFamily (k := Scalars (k := k)) (V₀ := V₀) (V₁ := V₁)
      (W₀ := OperatorCoefficients (k := k) (A := A)))
    (P : ModulePath (Scalars (k := k)) V₁) (N : ℕ) (y : V₀) :
    NearIdentity N (rawVelocityGauge Q P N y).series :=
  orderedGauge_near _ N (rawVelocity_coeff_below Q P N y)

/-- The leading coefficient is the original Laurent tangent vector in its native coefficient space. -/
theorem rawVelocityGauge_leading
    (Q : TangentFamily (k := Scalars (k := k)) (V₀ := V₀) (V₁ := V₁)
      (W₀ := OperatorCoefficients (k := k) (A := A)))
    (P : ModulePath (Scalars (k := k)) V₁) (N : ℕ) (hN : 0 < N) (y : V₀) :
    operatorCoordinates (PowerSeries.coeff N (rawVelocityGauge Q P N y).series) = Q.linear y := by
  rw [rawVelocityGauge, orderedGauge_leading _ N hN (rawVelocity_coeff_below Q P N y) _
    (rawVelocity_leading Q P N y), AddEquiv.apply_symm_apply]

end OrderedGauge

end EnvelopingIsomorphism.Deformation.Gauge.LaurentConjugation
