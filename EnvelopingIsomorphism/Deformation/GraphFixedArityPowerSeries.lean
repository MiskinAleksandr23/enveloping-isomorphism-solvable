import EnvelopingIsomorphism.FormalSeries.PowerSeriesGroupedMultilinear
import EnvelopingIsomorphism.Deformation.SymmetrizedGraphLaurent
import EnvelopingIsomorphism.Deformation.GraphFixedArityMaps
import EnvelopingIsomorphism.Deformation.Gauge.CanonicalGraphMCAlgebra
noncomputable section
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.GraphFixedArityPowerSeries
open scoped BigOperators Classical
open EnvelopingIsomorphism.FormalSeries
variable {k V Z : Type*} [Field k] [AddCommGroup V] [Module k V]
  [AddCommGroup Z] [Module k Z] {n : ℕ}
def doubleApplyLinear (x : Fin n → PowerSeriesModule (LaurentSeries k) (LaurentModule k V)) :
    MultilinearMap k (fun _ : Fin n ↦ V) Z →ₛₗ[(HahnSeries.C : k →+* LaurentSeries k)]
      PowerSeriesModule (LaurentSeries k) (LaurentModule k Z) where
  toFun F := PowerSeriesModule.applyMultilinear (LaurentModule.extendScalars F) x
  map_add' F G := by
    apply PowerSeriesModule.ext
    intro d
    simp only [PowerSeriesModule.coeffV_applyMultilinear, PowerSeriesModule.coeffV_add]
    simp only [← LaurentModule.applyMultilinearLinear_apply, map_add, Finset.sum_add_distrib,
      LaurentModule.extendScalars_apply]
  map_smul' c F := by
    apply PowerSeriesModule.ext
    intro d
    simp only [PowerSeriesModule.coeffV_applyMultilinear, PowerSeriesModule.coeffV_smul,
      LaurentModule.extendScalars_apply]
    simp only [← LaurentModule.applyMultilinearLinear_apply, map_smul,
      LaurentModule.constant_series_smul, Finset.smul_sum]

@[simp] theorem doubleApplyLinear_apply
    (x : Fin n → PowerSeriesModule (LaurentSeries k) (LaurentModule k V))
    (F : MultilinearMap k (fun _ : Fin n ↦ V) Z) :
    doubleApplyLinear x F = PowerSeriesModule.applyMultilinear (LaurentModule.extendScalars F) x := rfl

theorem doubleApply_domDomCongr (σ : Equiv.Perm (Fin n))
    (F : MultilinearMap k (fun _ : Fin n ↦ V) Z)
    (x : Fin n → PowerSeriesModule (LaurentSeries k) (LaurentModule k V)) :
    doubleApplyLinear x (F.domDomCongr σ) = doubleApplyLinear (x ∘ σ) F := by
  have he : LaurentModule.extendScalars (F.domDomCongr σ) =
      (LaurentModule.extendScalars F).domDomCongr σ := by
    apply MultilinearMap.ext
    intro y
    exact LaurentModule.applyMultilinear_domDomCongr σ F y
  change PowerSeriesModule.applyMultilinear _ x = _
  rw [he, PowerSeriesModule.applyMultilinear_domDomCongr]
  rfl

variable [CharZero k] {d : ℕ}
open GraphWeightedInsertion SymmetrizedGraphProfiles SymmetrizedGraphInsertion

theorem doubleApply_symmetrize (F : ProfileMap k d n)
    (α : PowerSeriesModule (LaurentSeries k) (LaurentModule k (Bivector (k := k) (d := d)))) :
    doubleApplyLinear (fun _ ↦ α) (symmetrize F) = doubleApplyLinear (fun _ ↦ α) F := by
  rw [SymmetrizedGraphLaurent.symmetrize_eq_sum, map_smulₛₗ, map_sum]
  simp only [doubleApply_domDomCongr, Function.comp_def, Finset.sum_const,
    Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul (LaurentSeries k), smul_smul, map_inv₀, map_natCast]
  have hn : (n.factorial : LaurentSeries k) ≠ 0 := by
    rw [← map_natCast (HahnSeries.C : k →+* LaurentSeries k)]
    exact HahnSeries.C_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))
  rw [inv_mul_cancel₀ hn, one_smul]


open GraphFixedArityMaps UniformBinaryGraphs GraphCoefficientProfiles GraphAssociatorProfiles
open PowerSeriesModule

omit [CharZero k] in
theorem doubleApply_castArity {N : ℕ} (h : n = N) (F : ProfileMap k d n)
    (α : PowerSeriesModule (LaurentSeries k) (LaurentModule k (Bivector (k := k) (d := d)))) :
    doubleApplyLinear (fun _ ↦ α) (castArity h F) = doubleApplyLinear (fun _ ↦ α) F := by
  cases h
  rfl

omit [CharZero k] in
theorem doubleApply_groupedInsertion {a b : ℕ}
    (B : Binary k (MvPolynomial (Fin d) k) →ₗ[k]
      Binary k (MvPolynomial (Fin d) k) →ₗ[k] Ternary k (MvPolynomial (Fin d) k))
    (F : BinaryProfileMap k d a) (G : BinaryProfileMap k d b)
    (α : PowerSeriesModule (LaurentSeries k) (LaurentModule k (Bivector (k := k) (d := d)))) :
    doubleApplyLinear (fun _ ↦ α) (groupedInsertion B F G) =
      PowerSeriesModule.applyBilinear (LaurentModule.extendBilinear B)
        (doubleApplyLinear (fun _ ↦ α) F) (doubleApplyLinear (fun _ ↦ α) G) :=
  PowerSeriesModule.applyMultilinear_groupedBilinear_laurent_diagonal B F G α

omit [CharZero k] in
theorem applyBilinear_sub_operation {R U W : Type*} [CommRing R]
    [AddCommGroup U] [Module R U] [AddCommGroup W] [Module R W]
    (B C : U →ₗ[R] U →ₗ[R] W) (x y : PowerSeriesModule R U) :
    PowerSeriesModule.applyBilinear (B - C) x y =
      PowerSeriesModule.applyBilinear B x y - PowerSeriesModule.applyBilinear C x y := by
  apply PowerSeriesModule.ext
  intro t
  simp only [PowerSeriesModule.coeffV_applyBilinear, LinearMap.sub_apply,
    PowerSeriesModule.coeffV_sub, Finset.sum_sub_distrib]

/-- Exact fixed-total-arity decomposition after both actual Laurent and t completions. -/
theorem evaluation_associator_double (N : ℕ) (w : (n : ℕ) → BinaryGraph n 2 → k)
    (α : PowerSeriesModule (LaurentSeries k) (LaurentModule k (Bivector (k := k) (d := d)))) :
    doubleApplyLinear (fun _ ↦ α)
      (evaluation (symmetrizedValue (k := k) (d := d)) (associatorProfile N w)) =
      ∑ a : Fin (N + 1), PowerSeriesModule.applyBilinear LaurentModule.insertBinarySeries
        (doubleApplyLinear (fun _ ↦ α) (binaryMap (w a)))
        (doubleApplyLinear (fun _ ↦ α) (binaryMap (w (N-a)))) := by
  rw [evaluation_associatorProfile_grouped, map_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [map_sub, doubleApply_castArity, doubleApply_castArity,
    doubleApply_symmetrize, doubleApply_symmetrize,
    doubleApply_groupedInsertion, doubleApply_groupedInsertion]
  rw [← applyBilinear_sub_operation]
  rfl

/-- Reindexing the finite degree split gives the actual natural antidiagonal. -/
theorem evaluation_associator_double_antidiagonal (N : ℕ)
    (w : (n : ℕ) → BinaryGraph n 2 → k)
    (α : PowerSeriesModule (LaurentSeries k) (LaurentModule k (Bivector (k := k) (d := d)))) :
    doubleApplyLinear (fun _ ↦ α)
      (evaluation (symmetrizedValue (k := k) (d := d)) (associatorProfile N w)) =
      ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal N,
        PowerSeriesModule.applyBilinear LaurentModule.insertBinarySeries
          (doubleApplyLinear (fun _ ↦ α) (binaryMap (w ab.1)))
          (doubleApplyLinear (fun _ ↦ α) (binaryMap (w ab.2))) := by
  rw [evaluation_associator_double,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, ← Fin.sum_univ_eq_sum_range]



open GraphMultilinearCurvature GraphCurvatureProfiles

/-- The two-slot Schouten map completes to the actual outer-t Laurent bracket convolution. -/
theorem doubleApply_bracketMap
    (α : PowerSeriesModule (LaurentSeries k) (LaurentModule k (Bivector (k := k) (d := d)))) :
    doubleApplyLinear (fun _ : Fin 2 ↦ α) (bracketMap (k := k) (d := d)) =
      PowerSeriesModule.applyBilinear (LaurentModule.extendBilinear (schoutenBracket k d 1 1)) α α := by
  apply PowerSeriesModule.ext
  intro t
  simp only [doubleApplyLinear_apply, PowerSeriesModule.coeffV_applyMultilinear,
    LaurentModule.extendScalars_apply, PowerSeriesModule.coeffV_applyBilinear]
  apply Finset.sum_nbij' (fun q ↦ (q 0, q 1)) (fun p ↦ ![p.1, p.2])
  · intro q hq
    simpa [Finset.mem_piAntidiag, Fin.sum_univ_two] using hq
  · intro p hp
    simpa [Finset.mem_piAntidiag, Fin.sum_univ_two] using hp
  · intro q hq
    funext i
    fin_cases i <;> rfl
  · intro p hp
    rfl
  · intro q hq
    have hy : (fun i : Fin 2 ↦ PowerSeriesModule.coeffV (q i) α) =
        ![PowerSeriesModule.coeffV (q 0) α, PowerSeriesModule.coeffV (q 1) α] := by
      funext i
      fin_cases i <;> rfl
    rw [hy, applyMultilinear_bracketMap]
    rfl

/-- The fixed source arity retains its actual curvature family and outer-t bracket convolution. -/
theorem doubleApply_groupedCurvatureMap
    (v : (j : ℕ) → (i : Fin (j + 1)) → CurvatureGraph i → k) (n : ℕ)
    (α : PowerSeriesModule (LaurentSeries k) (LaurentModule k (Bivector (k := k) (d := d)))) :
    doubleApplyLinear (fun _ ↦ α) (groupedCurvatureMap (v n)) =
      PowerSeriesModule.applyBilinear (LaurentModule.extendBilinear LinearMap.id)
        (doubleApplyLinear (fun _ ↦ α)
          (Gauge.PlacedMixedGraphTaylorCoefficients.curvatureFamily (fun _ _ ↦ Finset.univ) v n))
        ((HahnSeries.C (1/2 : k) : LaurentSeries k) •
          PowerSeriesModule.applyBilinear (LaurentModule.extendBilinear (schoutenBracket k d 1 1)) α α) := by
  rw [groupedCurvatureMap_eq_groupedBilinear]
  change PowerSeriesModule.applyMultilinear
    (LaurentModule.extendScalars (LaurentModule.groupedBilinear LinearMap.id _ _)) (fun _ ↦ α) = _
  rw [PowerSeriesModule.applyMultilinear_groupedBilinear_laurent_diagonal]
  change PowerSeriesModule.applyBilinear (LaurentModule.extendBilinear LinearMap.id)
    (doubleApplyLinear (fun _ ↦ α) _) (doubleApplyLinear (fun _ ↦ α) ((1/2 : k) • bracketMap)) = _
  rw [map_smulₛₗ, doubleApply_bracketMap]

/-- The scalar boundary relation gives the actual fixed-arity outer-t target/source identity. -/
theorem fixed_arity_boundary_relation
    {w : (j : ℕ) → BinaryGraph j 2 → k}
    {v : (j : ℕ) → (i : Fin (j + 1)) → CurvatureGraph i → k}
    (h : GraphBoundaryProfiles.ScalarBoundaryRelation w v) (n : ℕ)
    (α : PowerSeriesModule (LaurentSeries k) (LaurentModule k (Bivector (k := k) (d := d)))) :
    (∑ ab ∈ Finset.HasAntidiagonal.antidiagonal (n + 2),
      PowerSeriesModule.applyBilinear LaurentModule.insertBinarySeries
        (doubleApplyLinear (fun _ ↦ α) (binaryMap (w ab.1)))
        (doubleApplyLinear (fun _ ↦ α) (binaryMap (w ab.2)))) =
      PowerSeriesModule.applyBilinear (LaurentModule.extendBilinear LinearMap.id)
        (doubleApplyLinear (fun _ ↦ α)
          (Gauge.PlacedMixedGraphTaylorCoefficients.curvatureFamily (fun _ _ ↦ Finset.univ) v n))
        ((HahnSeries.C (1/2 : k) : LaurentSeries k) •
          PowerSeriesModule.applyBilinear (LaurentModule.extendBilinear (schoutenBracket k d 1 1)) α α) := by
  rw [← evaluation_associator_double_antidiagonal, boundaryRelation_source_multilinear h,
    doubleApply_symmetrize, doubleApply_groupedCurvatureMap]

/-- Every fixed total arity vanishes at an actual outer-t Laurent Poisson input. -/
theorem homogeneous_sum_zero
    {w : (j : ℕ) → BinaryGraph j 2 → k}
    {v : (j : ℕ) → (i : Fin (j + 1)) → CurvatureGraph i → k}
    (h : GraphBoundaryProfiles.ScalarBoundaryRelation w v)
    (α : PowerSeriesModule (LaurentSeries k) (LaurentModule k (Bivector (k := k) (d := d))))
    (hα : PowerSeriesModule.applyBilinear
      (LaurentModule.extendBilinear (schoutenBracket k d 1 1)) α α = 0) (N : ℕ) :
    (∑ ab ∈ Finset.HasAntidiagonal.antidiagonal N,
      PowerSeriesModule.applyBilinear LaurentModule.insertBinarySeries
        (doubleApplyLinear (fun _ ↦ α) (binaryMap (w ab.1)))
        (doubleApplyLinear (fun _ ↦ α) (binaryMap (w ab.2)))) = 0 := by
  rcases N with _ | (_ | n)
  · rw [← evaluation_associator_double_antidiagonal, symmetrized_associator_zero, map_zero]
  · rw [← evaluation_associator_double_antidiagonal, symmetrized_associator_one, map_zero]
  · rw [fixed_arity_boundary_relation h, hα, smul_zero]
    change PowerSeriesModule.extendBilinear _ _ 0 = 0
    exact map_zero _

/-- The homogeneous vanishing endpoint uses the existing actual canonical arity terms. -/
theorem canonical_homogeneous_sum_zero [Algebra ℝ k]
    (h : GraphBoundaryProfiles.CanonicalScalarBoundaryRelation (k := k))
    (α : PowerSeriesModule (LaurentSeries k) (LaurentModule k (Bivector (k := k) (d := d))))
    (hα : PowerSeriesModule.applyBilinear
      (LaurentModule.extendBilinear (schoutenBracket k d 1 1)) α α = 0) (N : ℕ) :
    (∑ ab ∈ Finset.HasAntidiagonal.antidiagonal N,
      PowerSeriesModule.applyBilinear LaurentModule.insertBinarySeries
        (Gauge.LaurentTaylorArityBounds.arityTerm (Gauge.CanonicalTangentCoefficients.mcFamily k d) α ab.1)
        (Gauge.LaurentTaylorArityBounds.arityTerm (Gauge.CanonicalTangentCoefficients.mcFamily k d) α ab.2)) = 0 := by
  have hh := homogeneous_sum_zero (d := d) h α hα N
  simpa only [binaryMap_canonical, doubleApplyLinear_apply,
    Gauge.LaurentTaylorArityBounds.arityTerm] using hh

end EnvelopingIsomorphism.Deformation.GraphFixedArityPowerSeries
