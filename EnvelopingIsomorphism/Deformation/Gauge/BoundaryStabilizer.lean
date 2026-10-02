import EnvelopingIsomorphism.Deformation.Gauge.ElementaryOperators
import EnvelopingIsomorphism.FormalSeries.PowerSeriesModuleBridge

/-! Genuine boundary stabilizers for complete associative bilinear families.
The generator uses the full deformed product, including all higher coefficients. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Gauge

open PowerSeries EnvelopingIsomorphism.FormalSeries PowerSeriesModule

section InnerSeries

variable {k V : Type*} [CommRing k] [AddCommGroup V] [Module k V]

def innerVectorSeries (B : PowerSeriesModule k (Binary k V)) (u : V) :
    PowerSeriesModule k (Module.End k V) :=
  linearApply B (single 0 u) - linearApply (flipBinarySeries B) (single 0 u)

/-- The full formal inner operator `[u,-]_B`, in the Hochschild degree -1 sign. -/
def innerSeries (B : PowerSeriesModule k (Binary k V)) (u : V) :
    PowerSeries (Module.End k V) :=
  PowerSeries.mk fun n ↦ coeffV n (innerVectorSeries B u)

@[simp] theorem coeff_innerSeries (B : PowerSeriesModule k (Binary k V)) (u : V) (n : ℕ) :
    coeff n (innerSeries B u) = differentialZero (coeffV n B) u := by
  rw [innerSeries, PowerSeries.coeff_mk, innerVectorSeries, coeffV_sub,
    coeffV_linearApply_single_zero, coeffV_linearApply_single_zero, coeffV_flipBinarySeries]
  rfl

theorem operatorSeries_innerSeries (B : PowerSeriesModule k (Binary k V)) (u : V) :
    operatorSeries (innerSeries B u) = innerVectorSeries B u := by
  ext n
  rw [coeffV_operatorSeries]
  simp [innerSeries]

/-- Coefficientwise construction agrees with the actual inner operator on the
complete vector-series algebra. -/
theorem actV_innerSeries (B : PowerSeriesModule k (Binary k V)) (u : V)
    (x : PowerSeriesModule k V) :
    actV (innerSeries B u) x = extendBinary B (single 0 u) x - extendBinary B x (single 0 u) := by
  rw [actV_eq_linearApply]
  change linearApply (operatorSeries (innerSeries B u)) x = _
  rw [operatorSeries_innerSeries, innerVectorSeries, map_sub, LinearMap.sub_apply]
  change extendBinary B (single 0 u) x - extendBinary (flipBinarySeries B) (single 0 u) x = _
  rw [← extendBinary_flip B x (single 0 u)]

/-- Associativity of the full family makes its inner operator a derivation. -/
theorem innerSeries_derivation (B : PowerSeriesModule k (Binary k V)) (u : V)
    (hB : ∀ x y z, extendBinary B (extendBinary B x y) z = extendBinary B x (extendBinary B y z))
    (x y : PowerSeriesModule k V) :
    actV (innerSeries B u) (extendBinary B x y) =
      extendBinary B (actV (innerSeries B u) x) y + extendBinary B x (actV (innerSeries B u) y) := by
  simp only [actV_innerSeries, map_sub, LinearMap.sub_apply]
  rw [hB, hB, hB]
  abel

theorem actV_X_pow (N : ℕ) (x : PowerSeriesModule k V) :
    actV (PowerSeries.X ^ N : PowerSeries (Module.End k V)) x =
      (PowerSeries.X ^ N : PowerSeries k) • x := by
  ext n
  rw [coeffV_actV, coeffV_series_smul]
  apply Finset.sum_congr rfl
  rintro ⟨i, j⟩ hij
  simp only [PowerSeries.coeff_X_pow]
  split_ifs <;> simp

/-- The exact stabilizer generator includes the full family B, shifted by t^N. -/
def boundaryVelocity (N : ℕ) (B : PowerSeriesModule k (Binary k V)) (u : V) :
    PowerSeries (Module.End k V) := PowerSeries.X ^ N * innerSeries B u

theorem boundaryVelocity_coeff_below (N : ℕ) (B : PowerSeriesModule k (Binary k V)) (u : V)
    (i : ℕ) (hi : i < N) : coeff i (boundaryVelocity N B u) = 0 := by
  simp [boundaryVelocity, PowerSeries.coeff_X_pow_mul', Nat.not_le.mpr hi]

@[simp] theorem boundaryVelocity_leading (N : ℕ) (B : PowerSeriesModule k (Binary k V)) (u : V) :
    coeff N (boundaryVelocity N B u) = differentialZero (coeffV 0 B) u := by
  simp [boundaryVelocity, PowerSeries.coeff_X_pow_mul']

theorem boundaryVelocity_constantCoeff {N : ℕ} (hN : 0 < N)
    (B : PowerSeriesModule k (Binary k V)) (u : V) : constantCoeff (boundaryVelocity N B u) = 0 := by
  simpa only [coeff_zero_eq_constantCoeff] using boundaryVelocity_coeff_below N B u 0 hN

theorem actV_boundaryVelocity (N : ℕ) (B : PowerSeriesModule k (Binary k V)) (u : V)
    (x : PowerSeriesModule k V) :
    actV (boundaryVelocity N B u) x = (PowerSeries.X ^ N : PowerSeries k) • actV (innerSeries B u) x := by
  rw [boundaryVelocity, actV_mul, actV_X_pow]

theorem boundaryVelocity_derivation (N : ℕ) (B : PowerSeriesModule k (Binary k V)) (u : V)
    (hB : ∀ x y z, extendBinary B (extendBinary B x y) z = extendBinary B x (extendBinary B y z))
    (x y : PowerSeriesModule k V) :
    actV (boundaryVelocity N B u) (extendBinary B x y) =
      extendBinary B (actV (boundaryVelocity N B u) x) y +
        extendBinary B x (actV (boundaryVelocity N B u) y) := by
  rw [actV_boundaryVelocity, innerSeries_derivation B u hB,
    actV_boundaryVelocity, actV_boundaryVelocity, smul_add]
  simp only [map_smul, LinearMap.smul_apply]

end InnerSeries

section Stabilizer

variable {k A : Type*} [CommRing k] [CommRing A] [Algebra k A] [Algebra ℚ k] [Algebra ℚ A]

/-- A genuine complete gauge unit with prescribed leading boundary. -/
def boundaryGauge (N : ℕ) (hN : 0 < N) (B : PowerSeriesModule k (Binary k A)) (u : A) :
    GaugeUnit (Module.End k A) :=
  correctionGauge N hN (boundaryVelocity N B u) (boundaryVelocity_coeff_below N B u)

@[simp] theorem boundaryGauge_series (N : ℕ) (hN : 0 < N)
    (B : PowerSeriesModule k (Binary k A)) (u : A) :
    (boundaryGauge N hN B u).series = exp (boundaryVelocity N B u) := rfl

theorem boundaryGauge_near (N : ℕ) (hN : 0 < N) (B : PowerSeriesModule k (Binary k A)) (u : A) :
    NearIdentity N (boundaryGauge N hN B u).series :=
  correctionGauge_near N hN _ _

@[simp] theorem boundaryGauge_leading (N : ℕ) (hN : 0 < N)
    (B : PowerSeriesModule k (Binary k A)) (u : A) :
    coeff N (boundaryGauge N hN B u).series = differentialZero (coeffV 0 B) u := by
  rw [boundaryGauge, correctionGauge_leading, boundaryVelocity_leading]

@[simp] theorem operator_boundaryGauge_apply (N : ℕ) (hN : 0 < N)
    (B : PowerSeriesModule k (Binary k A)) (u : A) (x : PowerSeriesModule k A) :
    operatorUnitEquiv (boundaryGauge N hN B u).val x = actV (exp (boundaryVelocity N B u)) x := by
  rw [operatorUnitEquiv_apply, operator_apply]
  rfl

/-- The boundary exponential preserves the actual deformed multiplication. -/
theorem boundaryGauge_intertwines (N : ℕ) (hN : 0 < N)
    (B : PowerSeriesModule k (Binary k A)) (u : A)
    (hB : ∀ x y z, extendBinary B (extendBinary B x y) z = extendBinary B x (extendBinary B y z))
    (x y : PowerSeriesModule k A) :
    operatorUnitEquiv (boundaryGauge N hN B u).val (extendBinary B x y) =
      extendBinary B (operatorUnitEquiv (boundaryGauge N hN B u).val x)
        (operatorUnitEquiv (boundaryGauge N hN B u).val y) := by
  simp only [operator_boundaryGauge_apply]
  exact PowerSeriesModuleBridge.exp_actV_extendBinary (boundaryVelocity N B u)
    (boundaryVelocity_constantCoeff hN B u) B (boundaryVelocity_derivation N B u hB) x y

/-- Boundaries yield genuine stabilizers, not only stabilizers of a finite jet. -/
theorem boundaryGauge_fixes (N : ℕ) (hN : 0 < N)
    (B : PowerSeriesModule k (Binary k A)) (u : A)
    (hB : ∀ x y z, extendBinary B (extendBinary B x y) z = extendBinary B x (extendBinary B y z)) :
    conjugateBinarySeries (boundaryGauge N hN B u).val B = B := by
  apply extendBinary_injective
  have hfix : conjugate (operatorUnitEquiv (boundaryGauge N hN B u).val) (extendBinary B) =
      extendBinary B :=
    (conjugate_eq_iff _ _ _).mpr (boundaryGauge_intertwines N hN B u hB)
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  rw [extendBinary_conjugateBinarySeries, hfix]

end Stabilizer

end EnvelopingIsomorphism.Deformation.Gauge
