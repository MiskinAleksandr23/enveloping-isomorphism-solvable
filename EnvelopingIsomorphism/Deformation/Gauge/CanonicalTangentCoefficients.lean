import EnvelopingIsomorphism.Deformation.Gauge.GraphFirstCoefficient
import EnvelopingIsomorphism.Deformation.Gauge.PlacedMixedFirstCoefficient
import EnvelopingIsomorphism.Deformation.Kontsevich.BinaryGeometricWeights
import EnvelopingIsomorphism.Deformation.Gauge.SymmetricMiddleExact

/-! Positive operator coefficients of the actual canonical graph tangent maps.
The velocity coefficient retains every distinguished vertex position. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

namespace EnvelopingIsomorphism.Deformation.Gauge.CanonicalTangentCoefficients

open EnvelopingIsomorphism.FormalSeries
open MiddleExactPerturbation
open scoped Classical

section Unary
universe u v
variable {k : Type u} {U V : Type v} [Field k] [AddCommGroup U] [Module k U]
  [AddCommGroup V] [Module k V]

def unaryCoefficient : MultilinearMap k (fun _ : Fin 1 ↦ U) V →ₗ[k] (U →ₗ[k] V) :=
  (MultilinearMap.ofSubsingletonₗ k k U V (0 : Fin 1)).symm.toLinearMap

theorem extendCochain_one (F : LaurentModule k (MultilinearMap k (fun _ : Fin 1 ↦ U) V))
    (x : LaurentModule k U) :
    LaurentModule.extendCochain 1 F (fun _ ↦ x) =
      LaurentModule.linearApply (LaurentModule.map unaryCoefficient F) x := by
  apply LaurentModule.ext
  intro d
  rw [LaurentModule.coeff_extendCochain, LaurentModule.coeff_linearApply]
  apply finsum_congr
  intro a
  split_ifs
  · change (LaurentModule.coeff F (a 0)) (fun i ↦ LaurentModule.coeff x (a i.succ)) =
      (LaurentModule.coeff F (a 0)) (fun _ ↦ LaurentModule.coeff x (a 1))
    congr 1
    funext i
    rw [Fin.eq_zero i]
    rfl
  · rfl

def placementLinearSeries (C : GraphTaylorFamily (k := k) (V := U) (W := V)) (π₀ : U) :
    OperatorSeries (k := k) U V :=
  PowerSeriesModule.map unaryCoefficient (placementOperatorCoefficients C π₀ 0)

theorem act_placementLinearSeries
    (C : GraphTaylorFamily (k := k) (V := U) (W := V)) (π₀ : U) :
    act (placementLinearSeries C π₀) = taylorLinear (laurentPlacementTaylorFamily C π₀) := by
  apply LinearMap.ext
  intro x
  change LaurentModule.linearApply (toLaurent (PowerSeriesModule.map unaryCoefficient
    (placementOperatorCoefficients C π₀ 0))) x =
    LaurentModule.extendCochain 1 (toLaurent (placementOperatorCoefficients C π₀ 0)) (fun _ ↦ x)
  rw [toLaurent_map, extendCochain_one]

theorem placementComponent_one_one
    (C : GraphTaylorFamily (k := k) (V := U) (W := V)) (π₀ x : U) :
    placementComponent C π₀ 1 1 (fun _ ↦ x) = C 1 (fun _ ↦ x) := by
  letI : Unique {s : Finset (Fin 1) // s.card = 1} :=
    { default := ⟨Finset.univ, by simp⟩
      uniq := fun s ↦ Subtype.ext (Finset.eq_univ_of_card s.val (by simp)) }
  rw [placementComponent_diagonal, Fintype.sum_unique]
  change C 1 (Finset.univ.piecewise (fun _ ↦ x) (fun _ ↦ π₀)) = _
  simp

@[simp] theorem coeff0_placementLinearSeries
    (C : GraphTaylorFamily (k := k) (V := U) (W := V)) (π₀ x : U) :
    PowerSeriesModule.coeffV 0 (placementLinearSeries C π₀) x = C 1 (fun _ ↦ x) := by
  change placementComponent C π₀ 1 1 (fun _ ↦ x) = _
  exact placementComponent_one_one C π₀ x

end Unary

variable (K : Type*) [Field K] [CharZero K] [Algebra ℝ K] (d : ℕ)

abbrev Polynomial := MvPolynomial (Fin d) K
abbrev Vector := Multiderivation K (Polynomial K d) 1
abbrev Bivector := Multiderivation K (Polynomial K d) 2

def mcFamily : GraphTaylorFamily (k := K) (V := Bivector K d) (W := Binary K (Polynomial K d)) :=
  GraphTaylorCoefficients.effectiveFamily (fun _ ↦ Finset.univ)
    (Kontsevich.GeometricWeights.binaryWeightOver K)

def starSeries (π₀ : Bivector K d) : PowerSeriesModule K (Binary K (Polynomial K d)) :=
  baseMCImage (mcFamily K d) π₀

def allVelocityGraphs (n : ℕ) (i : Fin (n + 1)) :
    Finset (PlacedMixedGraphTaylorCoefficients.Graph 1 i) := Finset.univ

def velocityFamily : GraphTaylorFamily (k := K) (V := Bivector K d)
    (W := Vector K d →ₗ[K] Unary K (Polynomial K d)) :=
  PlacedMixedGraphTaylorCoefficients.mapOutput (cochainOneEquiv K (Polynomial K d)).toLinearMap
    (PlacedMixedGraphTaylorCoefficients.canonicalFamily allVelocityGraphs)

def zeroSeries (π₀ : Bivector K d) : OperatorSeries (k := K) (Vector K d) (Unary K (Polynomial K d)) :=
  MixedGraphTaylorCoefficients.baseOperatorSeries (velocityFamily K d) π₀

def oneSeries (π₀ : Bivector K d) : OperatorSeries (k := K) (Bivector K d) (Binary K (Polynomial K d)) :=
  placementLinearSeries (mcFamily K d) π₀

omit [CharZero K] in
theorem act_zeroSeries (π₀ : Bivector K d) :
    act (zeroSeries K d π₀) =
      (PlacedMixedGraphTaylorCoefficients.canonicalVelocityTangentFamily allVelocityGraphs π₀).linear := rfl

omit [CharZero K] in
theorem act_oneSeries (π₀ : Bivector K d) :
    act (oneSeries K d π₀) = taylorLinear (laurentPlacementTaylorFamily (mcFamily K d) π₀) :=
  act_placementLinearSeries _ _

omit [CharZero K] in
@[simp] theorem coeff0_starSeries (π₀ : Bivector K d) :
    PowerSeriesModule.coeffV 0 (starSeries K d π₀) = LinearMap.mul K (Polynomial K d) := rfl

omit [CharZero K] in
theorem coeff0_zeroSeries (π₀ : Bivector K d) :
    PowerSeriesModule.coeffV 0 (zeroSeries K d π₀) = SymmetricMiddle.unaryInclusion := by
  apply LinearMap.ext
  intro D
  change PowerSeriesModule.coeffV 0
    (MixedGraphTaylorCoefficients.baseOperatorSeries
      (PlacedMixedGraphTaylorCoefficients.mapOutput (cochainOneEquiv K (Polynomial K d)).toLinearMap
        (PlacedMixedGraphTaylorCoefficients.canonicalFamily allVelocityGraphs)) π₀) D = _
  rw [PlacedMixedFirstCoefficient.baseOperatorSeries_zero allVelocityGraphs rfl]
  exact (SymmetricMiddle.unaryInclusion_eq_derivation D).symm

theorem coeff0_oneSeries (π₀ : Bivector K d) :
    PowerSeriesModule.coeffV 0 (oneSeries K d π₀) = SymmetricMiddle.binaryInclusion := by
  apply LinearMap.ext
  intro F
  rw [oneSeries, coeff0_placementLinearSeries]
  rw [mcFamily, GraphFirstCoefficient.effectiveFamily_one _ _ rfl
    (Kontsevich.GeometricWeights.binaryWeightOver_oneVertex K)]
  simp only [one_div]
  rfl

end EnvelopingIsomorphism.Deformation.Gauge.CanonicalTangentCoefficients
