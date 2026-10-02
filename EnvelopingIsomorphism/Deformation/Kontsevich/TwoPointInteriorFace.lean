import EnvelopingIsomorphism.Deformation.Kontsevich.ClusterSmoothForms
import EnvelopingIsomorphism.Deformation.Kontsevich.TwoInteriorBoundary
import EnvelopingIsomorphism.Deformation.Kontsevich.GraphFormProduct
import EnvelopingIsomorphism.Deformation.Kontsevich.TwoPointInsertionJacobian
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# The normalized two-interior-point face and its angular integral

The face is an actual scale-zero normalized cluster slice. The reference
internal edge restricts to the circle angular form. Circle orientation,
outward-normal orientation, and transport to native coordinates are kept
explicit rather than assigned to graph weights.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.TwoPointInteriorFace

open Set Topology
open scoped UpperHalfPlane

def pairMask : Finset (Fin 2) := Finset.univ

abbrev Free := ClusterFreeCoordinates (0 : Fin 2) 0 1 pairMask 0
abbrev Angular := ClusterAngularCoordinates (0 : Fin 2) 0 1 pairMask 0
abbrev Slice := NormalizedInteriorClusterSlice (0 : Fin 2) 0 pairMask 0 1
abbrev Face := {x : Slice // x.val.scale = 0}

private instance : IsEmpty (ClusterCoarseIndex (0 : Fin 2) 0 pairMask) :=
  inferInstanceAs (IsEmpty (ClusterCoarseIndex (0 : Fin 2) 0 Finset.univ))

private instance : IsEmpty (ClusterShapeIndex (0 : Fin 2) 1 pairMask) :=
  inferInstanceAs (IsEmpty (ClusterShapeIndex (0 : Fin 2) 1 Finset.univ))

def freeCircle (u : Circle) : Free := (0, 0, 0, u, 0)

@[simp] theorem freeCircle_radius (u : Circle) : (freeCircle u).radius = 0 := rfl

@[simp] theorem freeCircle_base (u : Circle) (j : Fin 2) : (freeCircle u).base j = Complex.I := by
  simp [ClusterFreeCoordinates.base, ClusterFreeCoordinates.representative, pairMask]

@[simp] theorem freeCircle_velocity (u : Circle) (j : Fin 2) :
    (freeCircle u).velocity j = if j = 0 then 0 else (u : ℂ) := by
  fin_cases j <;> simp [ClusterFreeCoordinates.velocity, freeCircle]

theorem freeCircle_openConditions (u : Circle) : (freeCircle u).OpenConditions := by
  have hall (j : Fin 2) : j ∈ pairMask := by simp [pairMask]
  have hsame (j k : Fin 2) : sameInteriorClusterBase pairMask j k := Or.inr ⟨hall j, hall k⟩
  refine ⟨⟨⟨0, hall 0⟩, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro j
    change 0 < ((freeCircle u).base j).im
    simp
  · intro j k h
    exact False.elim (h (hsame j k))
  · intro j k hjk hsame'
    change (freeCircle u).velocity j ≠ (freeCircle u).velocity k
    fin_cases j <;> fin_cases k <;> simp_all [freeCircle_velocity, u.coe_ne_zero, Ne.symm u.coe_ne_zero]
  · intro j
    exact Fin.elim0 j
  · intro j
    change (0 : ℝ) * ‖(freeCircle u).velocity j‖ < ((freeCircle u).base j).im
    simp
  · intro j k h
    exact False.elim (h (hsame j k))

def freeCircleDomain (u : Circle) : ClusterFreeDomain (0 : Fin 2) 0 1 pairMask 0 :=
  ⟨freeCircle u, le_rfl, freeCircle_openConditions u⟩

def nativeFreeHomeomorph : ClusterFreeDomain (0 : Fin 2) 0 1 pairMask 0 ≃ₜ Slice :=
  clusterFreeHomeomorph (by simp [pairMask]) (by simp [pairMask]) (by decide) (fun _ => rfl)

def circleFace (u : Circle) : Face := ⟨nativeFreeHomeomorph (freeCircleDomain u), rfl⟩

def faceDirection (x : Face) : Circle := x.val.freeCoordinates.2.2.2.1

@[simp] theorem faceDirection_circleFace (u : Circle) : faceDirection (circleFace u) = u := by
  change (ClusterFreeDomain.toSlice (by simp [pairMask]) (by simp [pairMask]) (by decide)
    (fun _ => rfl) (freeCircleDomain u)).freeCoordinates.2.2.2.1 = u
  rw [ClusterFreeDomain.freeCoordinates_toSlice]
  rfl

@[simp] theorem circleFace_faceDirection (x : Face) : circleFace (faceDirection x) = x := by
  apply Subtype.ext
  apply nativeFreeHomeomorph.symm.injective
  change nativeFreeHomeomorph.symm (nativeFreeHomeomorph (freeCircleDomain (faceDirection x))) = _
  rw [nativeFreeHomeomorph.symm_apply_apply]
  apply Subtype.ext
  exact Prod.ext (Subsingleton.elim _ _) (Prod.ext (Subsingleton.elim _ _)
    (Prod.ext (Subsingleton.elim _ _) (Prod.ext rfl x.property.symm)))

theorem continuous_circleFace : Continuous circleFace := by
  apply Continuous.subtype_mk
  apply nativeFreeHomeomorph.continuous.comp
  apply Continuous.subtype_mk
  unfold freeCircle
  fun_prop

theorem continuous_faceDirection : Continuous faceDirection := by
  unfold faceDirection
  fun_prop

/-- The actual normalized scale-zero two-point slice is exactly a circle. -/
def circleFaceHomeomorph : Circle ≃ₜ Face where
  toFun := circleFace
  invFun := faceDirection
  left_inv := faceDirection_circleFace
  right_inv := circleFace_faceDirection
  continuous_toFun := continuous_circleFace
  continuous_invFun := continuous_faceDirection

@[simp] theorem circleFace_base (u : Circle) (j : Fin 2) :
    ((circleFace u).val.val.datum.base j : ℂ) = Complex.I := by
  change ((ClusterFreeDomain.toSlice (by simp [pairMask]) (by simp [pairMask]) (by decide)
    (fun _ => rfl) (freeCircleDomain u)).val.datum.base j : ℂ) = _
  rw [ClusterFreeDomain.toSlice_base]
  exact freeCircle_base u j

@[simp] theorem circleFace_velocity (u : Circle) (j : Fin 2) :
    (circleFace u).val.val.datum.velocity j = if j = 0 then 0 else (u : ℂ) := by
  change (ClusterFreeDomain.toSlice (by simp [pairMask]) (by simp [pairMask]) (by decide)
    (fun _ => rfl) (freeCircleDomain u)).val.datum.velocity j = _
  rw [ClusterFreeDomain.toSlice_velocity]
  exact freeCircle_velocity u j

/-- This normalized face is the same actual added circle previously constructed
as the positive-radius limit in the compactification. -/
theorem circleFace_insertion_eq_boundaryPoint (u : Circle) :
    (circleFace u).val.insertion = twoInteriorBoundaryPoint u := by
  let D := (circleFace u).val.val.datum.toInteriorCollisionData
  have hb : D.doubledBase = twoInteriorBase := by
    funext v
    rcases v with (j | j) | j
    · exact circleFace_base u j
    · exact Fin.elim0 j
    · change star (((circleFace u).val.val.datum.base j : UpperHalfPlane) : ℂ) = -Complex.I
      rw [circleFace_base]
      simp
  have hv : D.doubledVelocity = twoInteriorVelocity u := by
    funext v
    rcases v with (j | j) | j
    · exact circleFace_velocity u j
    · exact Fin.elim0 j
    · change star ((circleFace u).val.val.datum.velocity j) = if j = 0 then 0 else star (u : ℂ)
      rw [circleFace_velocity]
      split_ifs <;> simp
  apply Subtype.ext
  change D.resolvedCoordinates 0 = linearCollisionCoordinates twoInteriorBase (twoInteriorVelocity u)
  rw [D.resolvedCoordinates_zero, hb, hv]

/-- The actual positive-angle map into the native angular/radial parameter space. -/
def angleMap : ℝ →L[ℝ] Angular :=
  TwoPointInsertionJacobian.coordinates.symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.id ℝ ℝ).prod (0 : ℝ →L[ℝ] ℝ))

@[simp] theorem angleMap_toFree (θ : ℝ) :
    (angleMap θ).toFree = freeCircle (Circle.exp θ) := rfl

def angleDomain (θ : ℝ) : ClusterAngularDomain (0 : Fin 2) 0 1 pairMask 0 :=
  ⟨angleMap θ, le_rfl, freeCircle_openConditions (Circle.exp θ)⟩

theorem chart_angleDomain_eq_circleFace (θ : ℝ) :
    ClusterAngularDomain.toCompactification (by simp [pairMask]) (by simp [pairMask])
      (by decide) (fun _ => rfl) (angleDomain θ) = (circleFace (Circle.exp θ)).val.insertion := rfl

/-- Every point of the actual added circle belongs to one of the already
constructed angular/radial compactification charts. -/
theorem exists_chart_at_circle (u : Circle) :
    ∃ θ : ℝ, Circle.exp θ = u ∧
      ∃ e : OpenPartialHomeomorph (ClusterAngularDomain (0 : Fin 2) 0 1 pairMask 0)
          (Compactification (0 : Fin 2) 0),
        angleDomain θ ∈ e.source ∧ e (angleDomain θ) = twoInteriorBoundaryPoint u := by
  obtain ⟨θ, hθ⟩ := Circle.exp_surjective u
  obtain ⟨e, he, hmap⟩ := ClusterAngularDomain.exists_chart_at_scale_zero
    (by simp [pairMask]) (by simp [pairMask]) (by decide) (fun _ => rfl) (angleDomain θ) rfl
  refine ⟨θ, hθ, e, he, ?_⟩
  rw [← hmap, chart_angleDomain_eq_circleFace, circleFace_insertion_eq_boundaryPoint, hθ]

abbrev referenceRatio : Angular → ℂ :=
  ClusterAngularCoordinates.internalRatio (i := (0 : Fin 2)) (a := 0) (b := 1)
    (S := pairMask) (m := 0) 0 1

theorem referenceRatio_angleMap : referenceRatio ∘ angleMap =
    fun θ : ℝ => circleParameter θ / (2 * Complex.I) := by
  funext θ
  change variableInternalClusterRegularizedRatio
    (ClusterAngularCoordinates.internalParameters 0 1 (angleMap θ)) = _
  simp [ClusterAngularCoordinates.internalParameters, variableInternalClusterRegularizedRatio,
    variableInternalClusterDenominator, circleParameter_eq, two_mul]

theorem differentiableAt_referenceRatio_angleMap (θ : ℝ) :
    DifferentiableAt ℝ referenceRatio (angleMap θ) := by
  have hd := ClusterAngularCoordinates.internalDenominator_face_ne_zero (angleMap θ)
    (freeCircle_openConditions (Circle.exp θ)) rfl (0 : Fin 2) 1
  exact ((contDiffAt_variableInternalClusterRegularizedRatio _ hd).comp (angleMap θ)
    (ClusterAngularCoordinates.contDiff_internalParameters (i := (0 : Fin 2))
      (a := 0) (b := 1) (S := pairMask) (m := 0) 0 1).contDiffAt).differentiableAt (by simp)

/-- A fixed nonzero complex scaling changes the angle by a constant and leaves
the actual circle pullback one-form unchanged. -/
theorem angularPullback_circle_div_const (c : ℂ) (hc : c ≠ 0) (θ : ℝ) :
    angularPullback (fun t : ℝ => circleParameter t / c) θ =
      ContinuousAlternatingMap.ofSubsingletonLIE (0 : Fin 1) (ContinuousLinearMap.id ℝ ℝ) := by
  have hdiff : DifferentiableAt ℝ (fun z : ℂ => z / c) (circleParameter θ) := by fun_prop
  have hcomp := angularPullback_comp_differentiable (fun z : ℂ => z / c) circleParameter θ hdiff
    (hasFDerivAt_circleParameter θ).differentiableAt
  have hcform : angularPullback (fun z : ℂ => z / c) (circleParameter θ) =
      angularForm (circleParameter θ) := by
    have h := angularPullback_clm_div (ContinuousLinearMap.id ℝ ℂ) c hc (circleParameter θ)
    exact h
  change angularPullback ((fun z : ℂ => z / c) ∘ circleParameter) θ = _
  rw [hcomp, hcform, (hasFDerivAt_circleParameter θ).fderiv]
  exact angularForm_circleParameter θ

/-- The reference internal edge on the actual two-point face, pulled back by
the positive real-angle coordinate. -/
def referenceCircleForm (θ : ℝ) : ℝ [⋀^Fin 1]→L[ℝ] ℝ :=
  (ClusterAngularCoordinates.internalEdgeForm (i := (0 : Fin 2)) (a := 0) (b := 1)
    (S := pairMask) (m := 0) 0 1 (angleMap θ)).compContinuousLinearMap angleMap

theorem referenceCircleForm_eq_dtheta (θ : ℝ) :
    referenceCircleForm θ =
      ContinuousAlternatingMap.ofSubsingletonLIE (0 : Fin 1) (ContinuousLinearMap.id ℝ ℝ) := by
  change (angularPullback referenceRatio (angleMap θ)).compContinuousLinearMap angleMap = _
  rw [angularPullback_comp_clm referenceRatio angleMap θ (differentiableAt_referenceRatio_angleMap θ),
    referenceRatio_angleMap]
  exact angularPullback_circle_div_const (2 * Complex.I) two_mul_I_ne_zero θ

def fiberDensity (θ : ℝ) : ℝ := referenceCircleForm θ (fun _ : Fin 1 => 1)

@[simp] theorem fiberDensity_eq_one (θ : ℝ) : fiberDensity θ = 1 := by
  rw [fiberDensity, referenceCircleForm_eq_dtheta]
  rfl

theorem intervalIntegral_fiberDensity :
    (∫ θ in (0 : ℝ)..(2 * Real.pi), fiberDensity θ) = 2 * Real.pi := by
  simp

/-- The actual positively parameterized circle angular integral is `2π`. -/
theorem integral_fiberDensity :
    (∫ θ in Set.Icc (0 : ℝ) (2 * Real.pi), fiberDensity θ) = 2 * Real.pi := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by positivity)]
  exact intervalIntegral_fiberDensity

/-- The chart orders angle before radius. The actual native outward-first
frame is positive, so the reference angular integral has the displayed sign
in this chart orientation. Native-coordinate transport has its separate
negative polar Jacobian, proved in `TwoPointInsertionJacobian`. -/
theorem outward_frame_and_circle_integral :
    ((ClusterAngularCoordinates.coordinateBasis (i := (0 : Fin 2)) (a := 0) (b := 1)
      (S := Finset.univ) (m := 0)).reindex TwoPointInsertionJacobian.indexEquiv).det
        ![TwoPointInsertionJacobian.coordinates.symm ClusterInsertionJacobian.outwardNormal,
          TwoPointInsertionJacobian.coordinates.symm ClusterInsertionJacobian.positiveAngleTangent] = 1 ∧
      (∫ θ in Set.Icc (0 : ℝ) (2 * Real.pi), fiberDensity θ) = 2 * Real.pi :=
  ⟨TwoPointInsertionJacobian.native_outward_angle_frame_det, integral_fiberDensity⟩

def fiberLinear (θ : ℝ) : ℝ →L[ℝ] ℝ :=
  (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := ℝ) (F := ℝ) (0 : Fin 1)).symm
    (referenceCircleForm θ)

@[simp] theorem fiberLinear_eq_id (θ : ℝ) : fiberLinear θ = ContinuousLinearMap.id ℝ ℝ := by
  rw [fiberLinear, referenceCircleForm_eq_dtheta]
  exact (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := ℝ) (F := ℝ) (0 : Fin 1)).symm_apply_apply _

def fiberCovectors (θ : ℝ) : Fin 1 → ℝ →L[ℝ] ℝ := fun _ => fiberLinear θ

@[simp] theorem fiberCovectors_density (θ : ℝ) :
    GraphFormProduct.ofCovectors (fiberCovectors θ) (fun _ : Fin 1 => (1 : ℝ)) = 1 := by
  rw [GraphFormProduct.ofCovectors_apply, Matrix.det_unique]
  simp [fiberCovectors]

section Product

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {r : ℕ}

/-- The actual determinant product of coarse covectors with the proved circle
one-form, with the circle slot last in the displayed product ordering. -/
def productForm (α : Fin r → E →L[ℝ] ℝ) (θ : ℝ) : (E × ℝ) [⋀^Fin (r + 1)]→L[ℝ] ℝ :=
  GraphFormProduct.ofCovectors (GraphFormProduct.productCovectors α (fiberCovectors θ))

theorem productForm_apply (α : Fin r → E →L[ℝ] ℝ) (θ : ℝ) (v : Fin r → E) :
    productForm α θ (GraphFormProduct.productVectors v (fun _ : Fin 1 => (1 : ℝ))) =
      GraphFormProduct.ofCovectors α v := by
  rw [productForm, GraphFormProduct.form_product_apply, fiberCovectors_density, mul_one]

/-- Edge and tangent reordering contribute their independent, explicit signs. -/
theorem productForm_permuted_apply (α : Fin r → E →L[ℝ] ℝ) (θ : ℝ) (v : Fin r → E)
    (σ τ : Equiv.Perm (Fin (r + 1))) :
    GraphFormProduct.ofCovectors
      (fun j => GraphFormProduct.productCovectors α (fiberCovectors θ) (σ j))
      (fun i => GraphFormProduct.productVectors v (fun _ : Fin 1 => (1 : ℝ)) (τ i)) =
        (Equiv.Perm.sign σ : ℝ) * (Equiv.Perm.sign τ : ℝ) * GraphFormProduct.ofCovectors α v := by
  rw [GraphFormProduct.form_product_permuted_apply, fiberCovectors_density, mul_one]

theorem fiber_integrable : MeasureTheory.IntegrableOn
    (fun θ => GraphFormProduct.ofCovectors (fiberCovectors θ) (fun _ : Fin 1 => (1 : ℝ)))
    (Set.Icc (0 : ℝ) (2 * Real.pi)) := by
  simp only [fiberCovectors_density]
  exact continuousOn_const.integrableOn_compact isCompact_Icc

/-- Actual product integration gives the circle factor `2π`, with a genuine
L1 hypothesis only on the coarse density. No Stokes or boundary identity is assumed. -/
theorem integral_product_circle {A : Type*} [MeasurableSpace A]
    (α : A → Fin r → E →L[ℝ] ℝ) (v : Fin r → E)
    (U : Set A) (μ : MeasureTheory.Measure A) [MeasureTheory.SFinite μ]
    (hα : MeasureTheory.IntegrableOn (fun x => GraphFormProduct.ofCovectors (α x) v) U μ) :
    (∫ z in U ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi),
      productForm (α z.1) z.2 (GraphFormProduct.productVectors v (fun _ : Fin 1 => (1 : ℝ)))
        ∂μ.prod MeasureTheory.volume) =
      (2 * Real.pi) * ∫ x in U, GraphFormProduct.ofCovectors (α x) v ∂μ := by
  have h := GraphFormProduct.integral_productDensity α fiberCovectors v
    (fun _ : Fin 1 => (1 : ℝ)) hα fiber_integrable
  have hcircle : (∫ θ in Set.Icc (0 : ℝ) (2 * Real.pi),
      GraphFormProduct.ofCovectors (fiberCovectors θ) (fun _ : Fin 1 => (1 : ℝ))) = 2 * Real.pi := by
    simpa only [fiberCovectors_density, fiberDensity_eq_one] using integral_fiberDensity
  rw [hcircle] at h
  exact h.trans (mul_comm _ _)

/-- The genuine circle product integral with both independent edge-order and
oriented-tangent-order signs retained. -/
theorem integral_product_circle_permuted {A : Type*} [MeasurableSpace A]
    (α : A → Fin r → E →L[ℝ] ℝ) (v : Fin r → E)
    (U : Set A) (μ : MeasureTheory.Measure A) [MeasureTheory.SFinite μ]
    (σ τ : Equiv.Perm (Fin (r + 1)))
    (hα : MeasureTheory.IntegrableOn (fun x => GraphFormProduct.ofCovectors (α x) v) U μ) :
    (∫ z in U ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi),
      GraphFormProduct.permutedProductDensity α fiberCovectors v (fun _ : Fin 1 => (1 : ℝ)) σ τ z
        ∂μ.prod MeasureTheory.volume) =
      (Equiv.Perm.sign σ : ℝ) * (Equiv.Perm.sign τ : ℝ) *
        ((2 * Real.pi) * ∫ x in U, GraphFormProduct.ofCovectors (α x) v ∂μ) := by
  have h := GraphFormProduct.integral_permutedProductDensity α fiberCovectors v
    (fun _ : Fin 1 => (1 : ℝ)) σ τ hα fiber_integrable
  have hcircle : (∫ θ in Set.Icc (0 : ℝ) (2 * Real.pi),
      GraphFormProduct.ofCovectors (fiberCovectors θ) (fun _ : Fin 1 => (1 : ℝ))) = 2 * Real.pi := by
    simpa only [fiberCovectors_density, fiberDensity_eq_one] using integral_fiberDensity
  rw [hcircle] at h
  exact h.trans (by ring)

end Product

end EnvelopingIsomorphism.Deformation.Kontsevich.TwoPointInteriorFace
