import EnvelopingIsomorphism.Deformation.Gauge.CanonicalTangentCoefficients
import EnvelopingIsomorphism.Deformation.Gauge.PositiveSourceOperators
import EnvelopingIsomorphism.Deformation.Gauge.PositiveTargetOperators
import EnvelopingIsomorphism.Deformation.Gauge.LowTangent
import EnvelopingIsomorphism.Deformation.Gauge.PositiveBlockOperators

/-! Exactness of the actual canonical low tangent at a positive-h Poisson base.
Only base-star associativity and the actual low chain identity remain geometric inputs. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

namespace EnvelopingIsomorphism.Deformation.Gauge.CanonicalTangentExactness

open EnvelopingIsomorphism.FormalSeries
open MiddleExactPerturbation
open CanonicalTangentCoefficients

variable (K : Type*) [Field K] [CharZero K] [Algebra ℝ K] (d : ℕ)
local instance : CharZero (LaurentSchouten.Scalars K) := LaurentSchouten.scalarCharZero

abbrev baseBivector (π₀ : Bivector K d) := LaurentModule.single (k := K) 1 π₀
abbrev baseStar (π₀ : Bivector K d) := toLaurent (starSeries K d π₀)

def zeroMap (π₀ : Bivector K d) :=
  (PlacedMixedGraphTaylorCoefficients.canonicalVelocityTangentFamily allVelocityGraphs π₀).linear

def oneMap (π₀ : Bivector K d) :=
  taylorLinear (laurentPlacementTaylorFamily (mcFamily K d) π₀)

/-- Associativity of the genuine canonical graph star product at the base. -/
def StarAssociative (π₀ : Bivector K d) : Prop :=
  ∀ a b c, LaurentConjugation.evaluateCoefficient (baseStar K d π₀)
      (LaurentConjugation.evaluateCoefficient (baseStar K d π₀) a b) c =
    LaurentConjugation.evaluateCoefficient (baseStar K d π₀) a
      (LaurentConjugation.evaluateCoefficient (baseStar K d π₀) b c)

/-- The one geometric chain identity used by the low cone. Both maps are the
actual canonical graph maps, and the source operator is exactly h ad(π₀). -/
def LowChainIdentity (π₀ : Bivector K d) : Prop :=
  (LaurentConjugation.differentialUnary (baseStar K d π₀)).comp (zeroMap K d π₀) =
    (oneMap K d π₀).comp (act (PositiveSourceOperators.C0 π₀))

variable (π₀ : Bivector K d)
variable (hπ : (polynomialSchoutenDGLA K d).laurent.IsMaurerCartan (baseBivector K d π₀))
variable (hμ : StarAssociative K d π₀) (hc : LowChainIdentity K d π₀)

theorem lowChainIdentity_iff_native : LowChainIdentity K d π₀ ↔
    ((LaurentConjugation.targetComplex (baseStar K d π₀) hμ).d 0 1).hom.comp (zeroMap K d π₀) =
      (oneMap K d π₀).comp
        ((LaurentSchouten.sourceComplex (baseBivector K d π₀) hπ).d 0 1).hom := by
  rw [LaurentConjugation.targetComplex_d_zero, ← PositiveSourceOperators.act_C0 π₀ hπ]
  rfl

/-- The canonical low tangent on the original Laurent source and target complexes. -/
def tangent : LowTangent
    (LaurentSchouten.sourceComplex (baseBivector K d π₀) hπ)
    (LaurentConjugation.targetComplex (baseStar K d π₀) hμ) where
  zero := zeroMap K d π₀
  one := oneMap K d π₀
  comm := by
    rw [LaurentConjugation.targetComplex_d_zero]
    change (LaurentConjugation.differentialUnary (baseStar K d π₀)).comp (zeroMap K d π₀) =
      (oneMap K d π₀).comp _
    rw [← PositiveSourceOperators.act_C0 π₀ hπ]
    exact hc

@[simp] theorem tangent_zero : (tangent K d π₀ hπ hμ hc).zero = zeroMap K d π₀ := rfl
@[simp] theorem tangent_one : (tangent K d π₀ hπ hμ hc).one = oneMap K d π₀ := rfl

omit [CharZero K] in
theorem zeroMap_eq_act : zeroMap K d π₀ = act (zeroSeries K d π₀) :=
  (act_zeroSeries K d π₀).symm

omit [CharZero K] in
theorem oneMap_eq_act : oneMap K d π₀ = act (oneSeries K d π₀) :=
  (act_oneSeries K d π₀).symm

open MiddleExactProduct PositiveBlockOperators

/-- The actual incoming positive-h low-cone operator. -/
def leftSeries : OperatorSeries (k := K) (CanonicalTangentCoefficients.Vector K d × Polynomial K d)
    (Bivector K d × Unary K (Polynomial K d)) :=
  blockSeries (-PositiveSourceOperators.C0 π₀) 0 (zeroSeries K d π₀)
    (PositiveTargetOperators.operatorNegOne (starSeries K d π₀))

/-- The actual outgoing positive-h low-cone operator. -/
def rightSeries : OperatorSeries (k := K) (Bivector K d × Unary K (Polynomial K d))
    (Multiderivation K (Polynomial K d) 3 × Binary K (Polynomial K d)) :=
  blockSeries (PositiveSourceOperators.C1 π₀) 0 (oneSeries K d π₀)
    (PositiveTargetOperators.operatorZero (starSeries K d π₀))

theorem coeff0_leftSeries : PowerSeriesModule.coeffV 0 (leftSeries K d π₀) =
    SymmetricMiddle.left := by
  rw [leftSeries, coeff0_blockSeries, PowerSeriesModule.coeffV_neg,
    PositiveSourceOperators.coeff_zero_C0, neg_zero, PowerSeriesModule.coeffV_zero,
    coeff0_zeroSeries, PositiveTargetOperators.coeff0_operatorNegOne _ (coeff0_starSeries K d π₀)]
  apply LinearMap.ext
  intro z
  simp [SymmetricMiddle.left]

theorem coeff0_rightSeries : PowerSeriesModule.coeffV 0 (rightSeries K d π₀) =
    SymmetricMiddle.right := by
  rw [rightSeries, coeff0_blockSeries, PositiveSourceOperators.coeff_zero_C1,
    PowerSeriesModule.coeffV_zero, coeff0_oneSeries,
    PositiveTargetOperators.coeff0_operatorZero _ (coeff0_starSeries K d π₀)]
  apply LinearMap.ext
  intro z
  simp [SymmetricMiddle.right]

theorem constant_middle_exact : LinearMap.range (PowerSeriesModule.coeffV 0 (leftSeries K d π₀)) =
    LinearMap.ker (PowerSeriesModule.coeffV 0 (rightSeries K d π₀)) := by
  rw [coeff0_leftSeries, coeff0_rightSeries]
  exact SymmetricMiddle.range_left_eq_ker_right

theorem productAct_leftSeries : productAct (leftSeries K d π₀) =
    (tangent K d π₀ hπ hμ hc).left := by
  apply LinearMap.ext
  rintro ⟨Y,u⟩
  rw [leftSeries, productAct_blockSeries, act_neg, act_zero]
  change (-act (PositiveSourceOperators.C0 π₀) Y + 0,
    act (zeroSeries K d π₀) Y + act (PositiveTargetOperators.operatorNegOne (starSeries K d π₀)) u) =
    (-((LaurentSchouten.sourceComplex (baseBivector K d π₀) hπ).d 0 1).hom Y,
      zeroMap K d π₀ Y + (show LaurentModule K (Unary K (Polynomial K d)) from
        ((LaurentConjugation.targetComplex (baseStar K d π₀) hμ).d (-1) 0).hom u))
  rw [add_zero, PositiveSourceOperators.act_C0 π₀ hπ,
    PositiveTargetOperators.act_operatorNegOne, ← zeroMap_eq_act,
    LaurentConjugation.targetComplex_d_negative_one]
  rfl

theorem productAct_rightSeries : productAct (rightSeries K d π₀) =
    (tangent K d π₀ hπ hμ hc).right := by
  apply LinearMap.ext
  rintro ⟨δ,X⟩
  rw [rightSeries, productAct_blockSeries, act_zero]
  change (act (PositiveSourceOperators.C1 π₀) δ + 0,
    act (oneSeries K d π₀) δ + act (PositiveTargetOperators.operatorZero (starSeries K d π₀)) X) =
    (((LaurentSchouten.sourceComplex (baseBivector K d π₀) hπ).d 1 2).hom δ,
      oneMap K d π₀ δ + (show LaurentModule K (Binary K (Polynomial K d)) from
        ((LaurentConjugation.targetComplex (baseStar K d π₀) hμ).d 0 1).hom X))
  rw [add_zero, PositiveSourceOperators.act_C1 π₀ hπ,
    PositiveTargetOperators.act_operatorZero, ← oneMap_eq_act,
    LaurentConjugation.targetComplex_d_zero]
  rfl

include hπ hμ hc in
/-- The formal convolution equation is derived from the genuine complexes and
actual graph low-chain identity; it is not a supplied exactness hypothesis. -/
theorem series_comp_eq_zero : PowerSeriesModule.linearCompose
    (rightSeries K d π₀) (leftSeries K d π₀) = 0 := by
  apply productAct_injective
  rw [productAct_comp, productAct_zero, productAct_leftSeries K d π₀ hπ hμ hc,
    productAct_rightSeries K d π₀ hπ hμ hc]
  apply LinearMap.ext
  intro z
  exact LowTangent.right_left (tangent K d π₀ hπ hμ hc) z

/-- Laurent perturbation of the proved commutative middle exactness, on the
original source/target products and with the actual canonical graph tangent. -/
instance tangent_isMiddleExact : (tangent K d π₀ hπ hμ hc).IsMiddleExact where
  range_eq_ker := by
    have h := laurent_middle_exact_product (leftSeries K d π₀) (rightSeries K d π₀)
      (series_comp_eq_zero K d π₀ hπ hμ hc) (constant_middle_exact K d π₀)
    rw [productAct_leftSeries K d π₀ hπ hμ hc,
      productAct_rightSeries K d π₀ hπ hμ hc] at h
    exact h

end EnvelopingIsomorphism.Deformation.Gauge.CanonicalTangentExactness
