import EnvelopingIsomorphism.Deformation.SchoutenAction
import EnvelopingIsomorphism.Deformation.Gauge.ElementaryOperators
import EnvelopingIsomorphism.FormalSeries.MonomialExpAction
import EnvelopingIsomorphism.FormalSeries.EndomorphismExpLog
import EnvelopingIsomorphism.FormalSeries.DerivationExp
import EnvelopingIsomorphism.FormalSeries.PowerSeriesModuleBridge
import EnvelopingIsomorphism.FormalSeries.AdjointMonomialExp

/-!
# Actual elementary exponentials of the Schouten action

The source operator is the complete exponential of a positive monomial in the
genuine degree-zero representation. Near-identity and leading coefficients
are proved for this operator, not supplied as fields of an abstract action.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Gauge

open EnvelopingIsomorphism.FormalSeries PowerSeriesModule PowerSeries
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

section GeneralLeading

variable {k V : Type*} [CommRing k] [AddCommGroup V] [Module k V]

private theorem gauge_apply_agree (G : GaugeUnit (Module.End k V)) {N : ℕ}
    (hG : NearIdentity N G.series) (B : PowerSeriesModule k V) :
    AgreeBelow N (operatorUnitEquiv G.val B) B := by
  change AgreeBelow N (operator G.series B) B
  have h : toJet N G.series = toJet N (1 : PowerSeries (Module.End k V)) :=
    hG.trans (map_one (toJet N)).symm
  simpa only [operator_one, LinearMap.id_apply] using operator_congr h B

private theorem gauge_apply_leading (G : GaugeUnit (Module.End k V)) {N : ℕ}
    (hN : 0 < N) (hG : NearIdentity N G.series) (B : PowerSeriesModule k V) :
    coeffV N (operatorUnitEquiv G.val B) =
      coeffV N B + (coeff N G.series) (coeffV 0 B) := by
  have h := coeffV_applyBilinear_left_constant
    (LinearMap.id : Module.End k V →ₗ[k] V →ₗ[k] V)
    (operatorSeries G.series) B 1 hN (operatorSeries_near hG)
  exact h

end GeneralLeading

variable {K : Type*} [Field K] [CharZero K] {d : ℕ}

abbrev SchoutenBivector (K : Type*) [Field K] (d : ℕ) :=
  Multiderivation K (PolynomialFunctions K d) 2

abbrev SchoutenVector (K : Type*) [Field K] (d : ℕ) :=
  Multiderivation K (PolynomialFunctions K d) 1

local instance sourceEndRing : Ring (Module.End K (SchoutenBivector K d)) :=
  @Module.End.instRing K (SchoutenBivector K d) inferInstance inferInstance inferInstance

local instance binaryEndRing : Ring (Module.End K (Binary K (PolynomialFunctions K d))) :=
  @Module.End.instRing K (Binary K (PolynomialFunctions K d)) inferInstance inferInstance inferInstance

local instance sourceSeriesAddGroup : AddCommGroup (PowerSeriesModule K (SchoutenBivector K d)) :=
  @HahnModule.instAddCommGroup ℕ K (SchoutenBivector K d) inferInstance inferInstance inferInstance

local instance schoutenRatTower (n : ℕ) :
    IsScalarTower ℚ K (Multiderivation K (PolynomialFunctions K d) n) where
  smul_assoc r s F := by
    apply Multiderivation.ext
    intro a
    change (r • s) • F a = r • (s • F a)
    exact smul_assoc r s (F a)

local instance schoutenRatComm (n : ℕ) :
    SMulCommClass K ℚ (Multiderivation K (PolynomialFunctions K d) n) where
  smul_comm s r F := by
    apply Multiderivation.ext
    intro a
    change s • (r • F a) = r • (s • F a)
    exact smul_comm s r (F a)

/-- The genuine degree-zero Schouten representation on bivectors. -/
def schoutenActionEnd (X : SchoutenVector K d) : Module.End K (SchoutenBivector K d) :=
  (polynomialSchoutenDGLA K d).zeroAction 1 X

@[simp] theorem schoutenActionEnd_apply (X : SchoutenVector K d) (F : SchoutenBivector K d) :
    schoutenActionEnd X F = schoutenVectorAction 1 X F := rfl

/-- Actual source operator `exp(t^N [X,-])`, with its exponential inverse. -/
def schoutenElementaryGauge (N : ℕ) (hN : 0 < N) (X : SchoutenVector K d) :
    GaugeUnit (Module.End K (SchoutenBivector K d)) :=
  elementaryGauge N hN (schoutenActionEnd X)

@[simp] theorem schoutenElementaryGauge_series (N : ℕ) (hN : 0 < N) (X : SchoutenVector K d) :
    (schoutenElementaryGauge N hN X).series = exp (monomial N (schoutenActionEnd X)) := rfl

theorem schoutenElementaryGauge_near (N : ℕ) (hN : 0 < N) (X : SchoutenVector K d) :
    NearIdentity N (schoutenElementaryGauge N hN X).series := elementaryGauge_near N hN _

theorem schoutenElementaryGauge_leading (N : ℕ) (hN : 0 < N) (X : SchoutenVector K d) :
    coeff N (schoutenElementaryGauge N hN X).series = schoutenActionEnd X := elementaryGauge_leading N hN _

/-- The actual scalar-series-linear source equivalence induced by the exponential. -/
def schoutenElementaryEquiv (N : ℕ) (hN : 0 < N) (X : SchoutenVector K d) :
    PowerSeriesModule K (SchoutenBivector K d) ≃ₗ[PowerSeries K]
      PowerSeriesModule K (SchoutenBivector K d) :=
  operatorUnitEquiv (k := K) (V := SchoutenBivector K d) (schoutenElementaryGauge N hN X).val

theorem schoutenElementaryEquiv_apply (N : ℕ) (hN : 0 < N) (X : SchoutenVector K d)
    (B : PowerSeriesModule K (SchoutenBivector K d)) :
    schoutenElementaryEquiv N hN X B =
      actV (k := K) (V := SchoutenBivector K d) (exp (monomial N (schoutenActionEnd X))) B :=
  operator_apply (k := K) (V := SchoutenBivector K d) _ _

/-- The inverse is the genuine negative exponential. -/
theorem schoutenElementaryEquiv_symm_apply (N : ℕ) (hN : 0 < N) (X : SchoutenVector K d)
    (B : PowerSeriesModule K (SchoutenBivector K d)) :
    (schoutenElementaryEquiv N hN X).symm B =
      actV (k := K) (V := SchoutenBivector K d) (exp (-monomial N (schoutenActionEnd X))) B :=
  operator_apply (k := K) (V := SchoutenBivector K d) _ _

theorem schoutenActionEnd_neg (X : SchoutenVector K d) : schoutenActionEnd (-X) = -schoutenActionEnd X :=
  map_neg ((polynomialSchoutenDGLA K d).zeroAction 1) X

theorem schoutenElementaryEquiv_neg (N : ℕ) (hN : 0 < N) (X : SchoutenVector K d) :
    schoutenElementaryEquiv N hN (-X) = (schoutenElementaryEquiv N hN X).symm := by
  apply LinearEquiv.ext
  intro B
  rw [schoutenElementaryEquiv_apply, schoutenElementaryEquiv_symm_apply, schoutenActionEnd_neg, map_neg]

/-- The affine perturbation action relative to the fixed bivector `π`. -/
def schoutenElementaryMotion (π : SchoutenBivector K d) (N : ℕ) (hN : 0 < N)
    (X : SchoutenVector K d) (b : PowerSeriesModule K (SchoutenBivector K d)) :
    PowerSeriesModule K (SchoutenBivector K d) :=
  schoutenElementaryEquiv N hN X (single (k := K) 0 π + b) - single (k := K) 0 π

theorem schoutenElementaryMotion_agree (π : SchoutenBivector K d) (N : ℕ) (hN : 0 < N)
    (X : SchoutenVector K d) (b : PowerSeriesModule K (SchoutenBivector K d)) :
    AgreeBelow (k := K) (V := SchoutenBivector K d) N (schoutenElementaryMotion π N hN X b) b := by
  intro i hi
  have h := gauge_apply_agree (k := K) (V := SchoutenBivector K d) (schoutenElementaryGauge N hN X)
    (schoutenElementaryGauge_near N hN X) (single (k := K) 0 π + b) i hi
  change coeffV (k := K) i (schoutenElementaryEquiv N hN X (single (k := K) 0 π + b)) =
    coeffV (k := K) i (single (k := K) 0 π + b) at h
  change coeffV (k := K) i
    (schoutenElementaryEquiv N hN X (single (k := K) 0 π + b) - single (k := K) 0 π) = _
  rw [coeffV_sub (k := K) (V := SchoutenBivector K d), h,
    coeffV_add (k := K) (V := SchoutenBivector K d)]
  abel

theorem schoutenElementaryMotion_positive (π : SchoutenBivector K d) (N : ℕ) (hN : 0 < N)
    (X : SchoutenVector K d) (b : PowerSeriesModule K (SchoutenBivector K d)) (hb : coeffV (k := K) 0 b = 0) :
    coeffV (k := K) 0 (schoutenElementaryMotion π N hN X b) = 0 :=
  (schoutenElementaryMotion_agree π N hN X b 0 hN).trans hb

theorem schoutenElementaryMotion_leading (π : SchoutenBivector K d) (N : ℕ) (hN : 0 < N)
    (X : SchoutenVector K d) (b : PowerSeriesModule K (SchoutenBivector K d)) (hb : coeffV (k := K) 0 b = 0) :
    coeffV (k := K) N (schoutenElementaryMotion π N hN X b) - coeffV (k := K) N b = schoutenActionEnd X π := by
  have h := gauge_apply_leading (k := K) (V := SchoutenBivector K d) (schoutenElementaryGauge N hN X) hN
    (schoutenElementaryGauge_near N hN X) (single (k := K) 0 π + b)
  change coeffV (k := K) N (schoutenElementaryEquiv N hN X (single (k := K) 0 π + b)) =
    coeffV (k := K) N (single (k := K) 0 π + b) +
      (coeff N (schoutenElementaryGauge N hN X).series) (coeffV (k := K) 0 (single (k := K) 0 π + b)) at h
  change coeffV (k := K) N
    (schoutenElementaryEquiv N hN X (single (k := K) 0 π + b) - single (k := K) 0 π) - coeffV (k := K) N b = _
  rw [coeffV_sub (k := K) (V := SchoutenBivector K d), h, schoutenElementaryGauge_leading]
  simp only [coeffV_add (k := K) (V := SchoutenBivector K d),
    coeffV_single (k := K) (V := SchoutenBivector K d), hb, add_zero]
  abel

/-- The leading displacement is `-[π, X]`, the twisted degree-zero differential term
when `π` is a Poisson base. -/
theorem schoutenElementaryMotion_leading_twist (π : SchoutenBivector K d) (N : ℕ) (hN : 0 < N)
    (X : SchoutenVector K d) (b : PowerSeriesModule K (SchoutenBivector K d)) (hb : coeffV (k := K) 0 b = 0) :
    coeffV (k := K) N (schoutenElementaryMotion π N hN X b) - coeffV (k := K) N b =
      -schoutenBracket K d 1 0 π X := by
  rw [schoutenElementaryMotion_leading π N hN X b hb]
  change schoutenBracket K d 0 1 X π = -schoutenBracket K d 1 0 π X
  have h := eq_of_heq (schoutenBracket_skew K d 0 1 X π)
  simpa only [Int.zero_mul, Int.negOnePow_zero, Units.val_one, Int.cast_one, neg_one_smul] using h

/-- Coefficientwise raw bivectors, in the existing completed binary-series model. -/
def rawBivectorSeries : PowerSeriesModule K (SchoutenBivector K d) →ₗ[PowerSeries K]
    PowerSeriesModule K (Binary K (PolynomialFunctions K d)) :=
  PowerSeriesModule.map (k := K) (V := SchoutenBivector K d)
    (W := Binary K (PolynomialFunctions K d)) rawBivectorLinearMap

/-- The actual source exponential intertwines with the exponential of the actual unary binary action. -/
theorem schoutenElementaryEquiv_raw (N : ℕ) (hN : 0 < N) (X : SchoutenVector K d)
    (B : PowerSeriesModule K (SchoutenBivector K d)) :
    rawBivectorSeries (schoutenElementaryEquiv N hN X B) =
      actV (k := K) (V := Binary K (PolynomialFunctions K d))
        (exp (monomial N (NilpotentConjugation.unaryActionEnd (Multiderivation.oneEquiv X).toLinearMap)))
        (rawBivectorSeries B) := by
  rw [schoutenElementaryEquiv_apply]
  apply map_actV_exp_monomial (k := K) (V := SchoutenBivector K d)
    (W := Binary K (PolynomialFunctions K d))
  intro F
  exact rawBivector_schoutenVectorAction X F

/-- The corresponding actual coordinate operator unit `exp(t^N D_X)`. -/
def schoutenCoordinateGauge (N : ℕ) (hN : 0 < N) (X : SchoutenVector K d) :
    GaugeUnit (Module.End K (PolynomialFunctions K d)) :=
  elementaryGauge N hN (Multiderivation.oneEquiv X).toLinearMap

/-- The image of the source exponential is actual conjugation of the full binary coefficient family. -/
theorem schoutenElementaryEquiv_raw_conjugate (N : ℕ) (hN : 0 < N) (X : SchoutenVector K d)
    (B : PowerSeriesModule K (SchoutenBivector K d)) :
    rawBivectorSeries (schoutenElementaryEquiv N hN X B) =
      conjugateBinarySeries (k := K) (V := PolynomialFunctions K d)
        (schoutenCoordinateGauge N hN X).val (rawBivectorSeries B) := by
  rw [schoutenElementaryEquiv_raw]
  exact AdjointMonomialExp.adjoint_monomial_exp_eq_conjugate
    (k := K) (V := PolynomialFunctions K d) (Multiderivation.oneEquiv X).toLinearMap N hN _

/-- A monomial series of genuine polynomial derivations. -/
def schoutenDerivationCoefficients (N : ℕ) (X : SchoutenVector K d) (j : ℕ) :
    Derivation K (PolynomialFunctions K d) (PolynomialFunctions K d) :=
  if j = N then Multiderivation.oneEquiv X else 0

omit [CharZero K] in
theorem schoutenDerivation_operators (N : ℕ) (X : SchoutenVector K d) :
    DerivationSeries.operators (schoutenDerivationCoefficients N X) =
      monomial N (Multiderivation.oneEquiv X).toLinearMap := by
  apply PowerSeries.ext
  intro j
  rw [DerivationSeries.coeff_operators, coeff_monomial]
  by_cases h : j = N <;> simp [schoutenDerivationCoefficients, h]

/-- The coordinate exponential is a genuine automorphism of the commutative formal polynomial algebra. -/
def schoutenCoordinateAutomorphism (N : ℕ) (hN : 0 < N) (X : SchoutenVector K d) :
    PowerSeries (PolynomialFunctions K d) ≃ₐ[PowerSeries K] PowerSeries (PolynomialFunctions K d) :=
  DerivationSeries.expAutomorphism (schoutenDerivationCoefficients N X)
    (by simp [schoutenDerivationCoefficients, Nat.ne_of_lt hN])

theorem schoutenCoordinateAutomorphism_apply (N : ℕ) (hN : 0 < N) (X : SchoutenVector K d)
    (p : PowerSeries (PolynomialFunctions K d)) :
    schoutenCoordinateAutomorphism N hN X p =
      EndomorphismSeries.act (exp (monomial N (Multiderivation.oneEquiv X).toLinearMap)) p := by
  rw [schoutenCoordinateAutomorphism, DerivationSeries.expAutomorphism_apply, schoutenDerivation_operators]

/-- The vector-series coordinate unit and the actual algebra automorphism are the same map. -/
theorem schoutenCoordinateGauge_matches_automorphism (N : ℕ) (hN : 0 < N) (X : SchoutenVector K d)
    (p : PowerSeriesModule K (PolynomialFunctions K d)) :
    PowerSeriesModuleBridge.moduleEquiv
      (operatorUnitEquiv (k := K) (V := PolynomialFunctions K d) (schoutenCoordinateGauge N hN X).val p) =
      schoutenCoordinateAutomorphism N hN X (PowerSeriesModuleBridge.moduleEquiv p) := by
  rw [operatorUnitEquiv_apply, operator_apply, PowerSeriesModuleBridge.moduleEquiv_actV,
    schoutenCoordinateAutomorphism_apply]
  rfl

/-- Raw bivector transport is intertwined by the actual coordinate algebra automorphism. -/
theorem schoutenElementary_intertwines (N : ℕ) (hN : 0 < N) (X : SchoutenVector K d)
    (B : PowerSeriesModule K (SchoutenBivector K d))
    (p q : PowerSeries (PolynomialFunctions K d)) :
    schoutenCoordinateAutomorphism N hN X (PowerSeriesModuleBridge.binaryBridge (rawBivectorSeries B) p q) =
      PowerSeriesModuleBridge.binaryBridge (rawBivectorSeries (schoutenElementaryEquiv N hN X B))
        (schoutenCoordinateAutomorphism N hN X p) (schoutenCoordinateAutomorphism N hN X q) := by
  let L := PowerSeriesModuleBridge.moduleEquiv (k := K) (A := PolynomialFunctions K d)
  let G := operatorUnitEquiv (k := K) (V := PolynomialFunctions K d) (schoutenCoordinateGauge N hN X).val
  have hi (x y : PowerSeriesModule K (PolynomialFunctions K d)) :
      G (extendBinary (rawBivectorSeries B) x y) =
        extendBinary (rawBivectorSeries (schoutenElementaryEquiv N hN X B)) (G x) (G y) := by
    rw [schoutenElementaryEquiv_raw_conjugate, extendBinary_conjugateBinarySeries, conjugate_apply]
    change G (extendBinary (rawBivectorSeries B) x y) =
      G (extendBinary (rawBivectorSeries B) (G.symm (G x)) (G.symm (G y)))
    simp only [LinearEquiv.symm_apply_apply]
  have h := congrArg L (hi (L.symm p) (L.symm q))
  simp only [L, G, schoutenCoordinateGauge_matches_automorphism,
    PowerSeriesModuleBridge.moduleEquiv_extendBinary, LinearEquiv.apply_symm_apply] at h
  exact h

/-- Translation to the fixed base bivector makes the actual source exponential an affine equivalence. -/
def schoutenElementaryAffineEquiv (π : SchoutenBivector K d) (N : ℕ) (hN : 0 < N)
    (X : SchoutenVector K d) : Equiv.Perm (PowerSeriesModule K (SchoutenBivector K d)) where
  toFun := schoutenElementaryMotion π N hN X
  invFun b := (schoutenElementaryEquiv N hN X).symm (single (k := K) 0 π + b) - single (k := K) 0 π
  left_inv b := by
    change (schoutenElementaryEquiv N hN X).symm
      (single (k := K) 0 π + (schoutenElementaryEquiv N hN X (single (k := K) 0 π + b) - single (k := K) 0 π)) -
      single (k := K) 0 π = b
    rw [← add_sub_assoc, add_sub_cancel_left, LinearEquiv.symm_apply_apply]
    abel
  right_inv b := by
    change schoutenElementaryEquiv N hN X
      (single (k := K) 0 π + ((schoutenElementaryEquiv N hN X).symm (single (k := K) 0 π + b) - single (k := K) 0 π)) -
      single (k := K) 0 π = b
    rw [← add_sub_assoc, add_sub_cancel_left, LinearEquiv.apply_symm_apply]
    abel

theorem schoutenElementaryAffineEquiv_symm_apply (π : SchoutenBivector K d) (N : ℕ) (hN : 0 < N)
    (X : SchoutenVector K d) (b : PowerSeriesModule K (SchoutenBivector K d)) :
    (schoutenElementaryAffineEquiv π N hN X).symm b = schoutenElementaryMotion π N hN (-X) b := by
  change (schoutenElementaryEquiv N hN X).symm (single (k := K) 0 π + b) - single (k := K) 0 π =
    schoutenElementaryEquiv N hN (-X) (single (k := K) 0 π + b) - single (k := K) 0 π
  rw [schoutenElementaryEquiv_neg]

theorem schoutenElementaryMotion_inverse (π : SchoutenBivector K d) (N : ℕ) (hN : 0 < N)
    (X : SchoutenVector K d) (b : PowerSeriesModule K (SchoutenBivector K d)) :
    schoutenElementaryMotion π N hN (-X) (schoutenElementaryMotion π N hN X b) = b := by
  rw [← schoutenElementaryAffineEquiv_symm_apply]
  exact (schoutenElementaryAffineEquiv π N hN X).symm_apply_apply b

theorem schoutenElementaryMotion_inverse_right (π : SchoutenBivector K d) (N : ℕ) (hN : 0 < N)
    (X : SchoutenVector K d) (b : PowerSeriesModule K (SchoutenBivector K d)) :
    schoutenElementaryMotion π N hN X (schoutenElementaryMotion π N hN (-X) b) = b := by
  rw [← schoutenElementaryAffineEquiv_symm_apply]
  exact (schoutenElementaryAffineEquiv π N hN X).apply_symm_apply b

/-- Positive perturbations, before imposing any Maurer-Cartan equation. -/
def PositiveSchoutenSeries (K : Type*) [Field K] (d : ℕ) :=
  {b : PowerSeriesModule K (SchoutenBivector K d) // coeffV (k := K) 0 b = 0}

/-- The actual elementary affine equivalence preserves the positive formal perturbation space. -/
def schoutenElementaryPositiveEquiv (π : SchoutenBivector K d) (N : ℕ) (hN : 0 < N)
    (X : SchoutenVector K d) : Equiv.Perm (PositiveSchoutenSeries K d) where
  toFun b := ⟨schoutenElementaryMotion π N hN X b.val,
    schoutenElementaryMotion_positive π N hN X b.val b.property⟩
  invFun b := ⟨schoutenElementaryMotion π N hN (-X) b.val,
    schoutenElementaryMotion_positive π N hN (-X) b.val b.property⟩
  left_inv b := Subtype.ext (schoutenElementaryMotion_inverse π N hN X b.val)
  right_inv b := Subtype.ext (schoutenElementaryMotion_inverse_right π N hN X b.val)

end EnvelopingIsomorphism.Deformation.Gauge
