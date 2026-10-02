import EnvelopingIsomorphism.Deformation.Kontsevich.ClusterAngularCoordinates
import Mathlib.Analysis.Analytic.Constructions

/-! Separate the common complex scale of one interior cluster from its unit shape.
The free/angle coordinate changes retain direction and radius. Cartesian complex
scale is used for actual analytic insertion, including scale zero; it is not
claimed to be an invertible polar coordinate change at that zero. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.ComplexClusterScaleCoordinates

open Topology

variable {n m : ℕ} {i a b : Fin n} {S : Finset (Fin n)}

abbrev UnitShape (a b : Fin n) (S : Finset (Fin n)) := ClusterShapeIndex a b S → ℂ

/-- The first marked unit-shape coordinate is zero and the second is one. -/
def unitShape (η : UnitShape a b S) (j : Fin n) : ℂ :=
  if hja : j = a then 0 else if hjb : j = b then 1
  else if hj : j ∈ S then η ⟨j, hj, hja, hjb⟩ else 0

@[simp] theorem unitShape_anchor (η : UnitShape a b S) : unitShape η a = 0 := by
  simp [unitShape]

theorem unitShape_reference (η : UnitShape a b S) (hba : b ≠ a) : unitShape η b = 1 := by
  simp [unitShape, hba]

@[simp] theorem unitShape_free (η : UnitShape a b S) (j : ClusterShapeIndex a b S) :
    unitShape η j.val = η j := by
  simp only [unitShape, dif_neg j.property.2.1, dif_neg j.property.2.2, dif_pos j.property.1]
  exact congrArg η (Subtype.ext rfl)

/-- The product now stores unit-shape coordinates, retaining the original direction and radius. -/
abbrev PolarCoordinates (i a b : Fin n) (S : Finset (Fin n)) (m : ℕ) :=
  (ClusterCoarseIndex i a S → ℂ) × UnitShape a b S × (Fin m → ℝ) × Circle × ℝ

def toUnitFree (x : ClusterFreeCoordinates i a b S m) : PolarCoordinates i a b S m :=
  (x.1, fun j ↦ ((x.2.2.2.1)⁻¹ : Circle) * x.2.1 j, x.2.2.1, x.2.2.2.1, x.2.2.2.2)

def toNativeFree (x : PolarCoordinates i a b S m) : ClusterFreeCoordinates i a b S m :=
  (x.1, fun j ↦ (x.2.2.2.1 : ℂ) * x.2.1 j, x.2.2.1, x.2.2.2.1, x.2.2.2.2)

/-- The genuine coordinate homeomorphism on the circle/radius product. -/
def freeHomeomorph : ClusterFreeCoordinates i a b S m ≃ₜ PolarCoordinates i a b S m where
  toFun := toUnitFree
  invFun := toNativeFree
  left_inv x := by simp [toUnitFree, toNativeFree]
  right_inv x := by simp [toUnitFree, toNativeFree]
  continuous_toFun := by unfold toUnitFree; fun_prop
  continuous_invFun := by unfold toNativeFree; fun_prop

/-- In these coordinates every native cluster velocity carries the same circle factor. -/
theorem velocity_toNativeFree (x : PolarCoordinates i a b S m) (j : Fin n) :
    (toNativeFree x).velocity j = (x.2.2.2.1 : ℂ) * unitShape x.2.1 j := by
  unfold ClusterFreeCoordinates.velocity unitShape
  split_ifs <;> simp [toNativeFree]

/-- The actual inverse coordinate change normalizes the entire native shape. -/
theorem unitShape_toUnitFree (x : ClusterFreeCoordinates i a b S m) (j : Fin n) :
    unitShape (toUnitFree x).2.1 j = (x.2.2.2.1 : ℂ)⁻¹ * x.velocity j := by
  have h := velocity_toNativeFree (toUnitFree x) j
  have hinv : toNativeFree (toUnitFree x) = x := freeHomeomorph.left_inv x
  rw [hinv] at h
  rw [h]
  simp [toUnitFree]

abbrev AngularCoordinates (i a b : Fin n) (S : Finset (Fin n)) (m : ℕ) :=
  (ClusterCoarseIndex i a S → ℂ) × UnitShape a b S × (Fin m → ℝ) × ℝ × ℝ

def toUnitAngular (x : ClusterAngularCoordinates i a b S m) : AngularCoordinates i a b S m :=
  (x.1, fun j ↦ (circleParameter x.2.2.2.1)⁻¹ * x.2.1 j, x.2.2.1, x.2.2.2.1, x.2.2.2.2)

def toNativeAngular (x : AngularCoordinates i a b S m) : ClusterAngularCoordinates i a b S m :=
  (x.1, fun j ↦ circleParameter x.2.2.2.1 * x.2.1 j, x.2.2.1, x.2.2.2.1, x.2.2.2.2)

/-- The smooth coordinate change on actual real-angle covers, with inverse. -/
def angularEquiv : ClusterAngularCoordinates i a b S m ≃ AngularCoordinates i a b S m where
  toFun := toUnitAngular
  invFun := toNativeAngular
  left_inv x := by simp [toUnitAngular, toNativeAngular, circleParameter_ne_zero]
  right_inv x := by simp [toUnitAngular, toNativeAngular, circleParameter_ne_zero]

@[fun_prop] theorem contDiff_toUnitAngular :
    ContDiff ℝ ⊤ (toUnitAngular : ClusterAngularCoordinates i a b S m → _) := by
  have hphase : ContDiff ℝ ⊤ (fun x : ClusterAngularCoordinates i a b S m ↦ circleParameter x.2.2.2.1) :=
    contDiff_circleParameter.comp (by fun_prop)
  unfold toUnitAngular
  apply ContDiff.prodMk (by fun_prop)
  apply ContDiff.prodMk
  · apply contDiff_pi.mpr
    intro j
    exact (hphase.inv (fun x ↦ circleParameter_ne_zero _)).mul (by fun_prop)
  · fun_prop

@[fun_prop] theorem contDiff_toNativeAngular :
    ContDiff ℝ ⊤ (toNativeAngular : AngularCoordinates i a b S m → _) := by
  have hphase : ContDiff ℝ ⊤ (fun x : AngularCoordinates i a b S m ↦ circleParameter x.2.2.2.1) :=
    contDiff_circleParameter.comp (by fun_prop)
  unfold toNativeAngular
  apply ContDiff.prodMk (by fun_prop)
  apply ContDiff.prodMk
  · apply contDiff_pi.mpr
    intro j
    exact hphase.mul (by fun_prop)
  · fun_prop

/-- The unit-shape angular change agrees with the existing native circle parameter. -/
theorem toUnitAngular_toFree (x : ClusterAngularCoordinates i a b S m) :
    ClusterAngularCoordinates.toFree (toUnitAngular x) = toUnitFree x.toFree := by
  simp [ClusterAngularCoordinates.toFree, toUnitAngular, toUnitFree, circleParameter_eq]

theorem toNativeAngular_toFree (x : AngularCoordinates i a b S m) :
    (toNativeAngular x).toFree = toNativeFree (ClusterAngularCoordinates.toFree x) := by
  simp [ClusterAngularCoordinates.toFree, toNativeAngular, toNativeFree, circleParameter_eq]

/-- Exact native velocity formula after the genuine smooth shape change. -/
theorem velocity_toNativeAngular (x : AngularCoordinates i a b S m) (j : Fin n) :
    (toNativeAngular x).toFree.velocity j = circleParameter x.2.2.2.1 * unitShape x.2.1 j := by
  rw [toNativeAngular_toFree, velocity_toNativeFree]
  rw [circleParameter_eq]
  rfl

/-- In the new coordinates normalized internal differences depend only on η;
there is no remaining angular or radial dependence. -/
theorem normalized_velocity_difference (x : AngularCoordinates i a b S m) (j k : Fin n) :
    (circleParameter x.2.2.2.1)⁻¹ *
      ((toNativeAngular x).toFree.velocity j - (toNativeAngular x).toFree.velocity k) =
      unitShape x.2.1 j - unitShape x.2.1 k := by
  rw [velocity_toNativeAngular, velocity_toNativeAngular, ← mul_sub]
  simp [circleParameter_ne_zero]

/-- The common complex cluster scale. -/
def complexScale (r θ : ℝ) : ℂ := (r : ℂ) * circleParameter θ

@[simp] theorem norm_complexScale (r θ : ℝ) : ‖complexScale r θ‖ = |r| := by
  simp [complexScale, circleParameter_eq]

/-- Genuine Cartesian complex variables, including w=0. -/
abbrev CartesianCoordinates (a b : Fin n) (S : Finset (Fin n)) := ℂ × UnitShape a b S × ℂ

/-- Polynomial insertion in the Cartesian complex scale; defined also at w=0. -/
def insertion (x : CartesianCoordinates a b S) (j : Fin n) : ℂ := x.1 + x.2.2 * unitShape x.2.1 j

@[simp] theorem insertion_zero (z : ℂ) (η : UnitShape a b S) (j : Fin n) :
    insertion (z, η, 0) j = z := by simp [insertion]

theorem insertion_difference (x : CartesianCoordinates a b S) (j k : Fin n) :
    insertion x j - insertion x k = x.2.2 * (unitShape x.2.1 j - unitShape x.2.1 k) := by
  unfold insertion
  ring

theorem analyticAt_unitShape (j : Fin n) (η : UnitShape a b S) :
    AnalyticAt ℂ (fun η : UnitShape a b S ↦ unitShape η j) η := by
  unfold unitShape
  split_ifs with hja hjb hj
  · exact analyticAt_const
  · exact analyticAt_const
  · exact (ContinuousLinearMap.proj (R := ℂ)
      (φ := fun _ : ClusterShapeIndex a b S ↦ ℂ) ⟨j, hj, hja, hjb⟩).analyticAt η
  · exact analyticAt_const

/-- Joint complex analyticity of the actual insertion, including Cartesian scale zero. -/
theorem analyticAt_insertion (j : Fin n) (x : CartesianCoordinates a b S) :
    AnalyticAt ℂ (fun x : CartesianCoordinates a b S ↦ insertion x j) x := by
  have hη : AnalyticAt ℂ (fun y : CartesianCoordinates a b S ↦ y.2.1) x :=
    (analyticAt_fst (p := x.2)).comp (analyticAt_snd (p := x))
  have hw : AnalyticAt ℂ (fun y : CartesianCoordinates a b S ↦ y.2.2) x :=
    (analyticAt_snd (p := x.2)).comp (analyticAt_snd (p := x))
  have hu : AnalyticAt ℂ (fun y : CartesianCoordinates a b S ↦ unitShape y.2.1 j) x :=
    (analyticAt_unitShape j x.2.1).comp (f := fun y : CartesianCoordinates a b S ↦ y.2.1) hη
  exact analyticAt_fst.add (hw.mul hu)

/-- Actual native insertion equals Cartesian insertion with w=r exp(iθ). -/
theorem native_insertion (x : AngularCoordinates i a b S m) (j : Fin n) :
    (toNativeAngular x).toFree.base j +
      ((toNativeAngular x).toFree.radius : ℂ) * (toNativeAngular x).toFree.velocity j =
    insertion ((toNativeAngular x).toFree.base j, x.2.1, complexScale x.2.2.2.2 x.2.2.2.1) j := by
  rw [velocity_toNativeAngular]
  simp only [insertion, complexScale, ClusterFreeCoordinates.radius,
    ClusterAngularCoordinates.toFree, toNativeAngular]
  ring

/-- For two labels in the same cluster, all native pair differences carry w. -/
theorem native_internal_difference (x : AngularCoordinates i a b S m) (j k : Fin n)
    (hj : j ∈ S) (hk : k ∈ S) :
    ((toNativeAngular x).toFree.base j +
      ((toNativeAngular x).toFree.radius : ℂ) * (toNativeAngular x).toFree.velocity j) -
    ((toNativeAngular x).toFree.base k +
      ((toNativeAngular x).toFree.radius : ℂ) * (toNativeAngular x).toFree.velocity k) =
      complexScale x.2.2.2.2 x.2.2.2.1 * (unitShape x.2.1 j - unitShape x.2.1 k) := by
  rw [native_insertion, native_insertion,
    ClusterFreeCoordinates.base_eq_of_same _ (Or.inr ⟨hj, hk⟩)]
  exact insertion_difference _ j k

/-- With unit shape held fixed, the actual angular derivative has an explicit
factor r. This conclusion is unavailable if the native free velocities are held fixed. -/
theorem hasDerivAt_angular_insertion (z : ℂ) (η : UnitShape a b S) (r θ : ℝ) (j : Fin n) :
    HasDerivAt (fun t ↦ insertion (z, η, complexScale r t) j)
      ((r : ℂ) * (circleParameter θ * Complex.I * unitShape η j)) θ := by
  have hp : HasDerivAt circleParameter (circleParameter θ * Complex.I) θ := by
    simpa [circleParameterTangent_apply] using (hasFDerivAt_circleParameter θ).hasDerivAt
  simpa only [insertion, complexScale, mul_assoc] using
    HasDerivAt.const_add z ((HasDerivAt.const_mul (r : ℂ) hp).mul_const (unitShape η j))

/-- The precise radial gain of the angular insertion derivative. -/
theorem norm_angular_derivative (z : ℂ) (η : UnitShape a b S) (r θ : ℝ) (j : Fin n) :
    ‖deriv (fun t ↦ insertion (z, η, complexScale r t) j) θ‖ = |r| * ‖unitShape η j‖ := by
  rw [(hasDerivAt_angular_insertion z η r θ j).deriv]
  simp [circleParameter_eq]

end EnvelopingIsomorphism.Deformation.Kontsevich.ComplexClusterScaleCoordinates
