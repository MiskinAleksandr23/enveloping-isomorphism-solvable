import EnvelopingIsomorphism.Deformation.Kontsevich.ClusterAngularChart
import EnvelopingIsomorphism.Deformation.Kontsevich.ClusterExternalForms

/-!
# Actual smooth edge forms in the finite angular/radial cluster coordinates

Internal edges use the proved radial regularization. External edges use the
ordinary harmonic pullback. These forms are smooth in all free real coordinates
through the simple-cluster face and agree with the actual harmonic forms at
positive admissible radius.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich

open ComplexConjugate

theorem angularPullback_comp_differentiable {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → ℂ) (g : F → E) (x : F) (hf : DifferentiableAt ℝ f (g x))
    (hg : DifferentiableAt ℝ g x) :
    angularPullback (f ∘ g) x =
      (angularPullback f (g x)).compContinuousLinearMap (fderiv ℝ g x) := by
  rw [angularPullback, fderiv_comp x hf hg]
  ext v
  rfl

theorem extDeriv_angularPullback {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℂ) (x : E) (hf : ContDiffAt ℝ ⊤ f x) (hzero : f x ≠ 0) :
    extDeriv (angularPullback f) x = 0 := by
  change extDeriv (fun y => (angularForm (f y)).compContinuousLinearMap (fderiv ℝ f y)) x = 0
  rw [extDeriv_pullback (f := f) (x := x)
    ((contDiffAt_angularForm hzero).differentiableAt (by simp)) hf (by simp), extDeriv_angularForm hzero]
  ext v
  rfl

namespace ClusterAngularCoordinates

variable {n m : ℕ} {i a b : Fin n} {S : Finset (Fin n)}

def position (x : ClusterAngularCoordinates i a b S m) (j : Fin n) : ℂ :=
  x.toFree.base j + (x.toFree.radius : ℂ) * x.toFree.velocity j

def targetBase (x : ClusterAngularCoordinates i a b S m) : Fin n ⊕ Fin m → ℂ
  | Sum.inl j => x.toFree.base j
  | Sum.inr j => (x.2.2.1 j : ℂ)

def actualPair (j : Fin n) (v : Fin n ⊕ Fin m) (x : ClusterAngularCoordinates i a b S m) : ℂ × ℂ :=
  (x.position j, match v with
    | Sum.inl k => x.position k
    | Sum.inr k => (x.2.2.1 k : ℂ))

@[fun_prop] theorem contDiff_actualPair (j : Fin n) (v : Fin n ⊕ Fin m) :
    ContDiff ℝ ⊤ (actualPair (i := i) (a := a) (b := b) (S := S) j v) := by
  cases v with
  | inl k => exact (contDiff_position j).prodMk (contDiff_position k)
  | inr k => exact (contDiff_position j).prodMk (Complex.ofRealCLM.contDiff.comp (by fun_prop))

theorem position_im_pos (x : ClusterAngularCoordinates i a b S m)
    (hx : x.toFree.OpenConditions) (hr : 0 ≤ x.toFree.radius) (j : Fin n) : 0 < (x.position j).im := by
  have hvel := (abs_le.mp (Complex.abs_im_le_norm (x.toFree.velocity j))).1
  have hmul := mul_le_mul_of_nonneg_left hvel hr
  have hbound := hx.2.1 j
  simp only [position, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, add_zero]
  nlinarith

theorem actualPair_denominator_ne_zero (x : ClusterAngularCoordinates i a b S m)
    (hx : x.toFree.OpenConditions) (hr : 0 ≤ x.toFree.radius) (j : Fin n) (v : Fin n ⊕ Fin m) :
    (actualPair j v x).2 - conj (actualPair j v x).1 ≠ 0 := by
  apply harmonicDenominator_ne_zero (x.position_im_pos hx hr j)
  cases v with
  | inl k => exact (x.position_im_pos hx hr k).le
  | inr k => simp [actualPair]

def actualEdgeForm (j : Fin n) (v : Fin n ⊕ Fin m) (x : ClusterAngularCoordinates i a b S m) :
    ClusterAngularCoordinates i a b S m [⋀^Fin 1]→L[ℝ] ℝ :=
  angularPullback (fun y => harmonicRatio (actualPair j v y).1 (actualPair j v y).2) x

theorem actualEdgeForm_eq_pullback (x : ClusterAngularCoordinates i a b S m)
    (hx : x.toFree.OpenConditions) (hr : 0 ≤ x.toFree.radius) (j : Fin n) (v : Fin n ⊕ Fin m) :
    actualEdgeForm j v x = (harmonicAngleForm (actualPair j v x)).compContinuousLinearMap
      (fderiv ℝ (actualPair j v) x) :=
  (harmonicAngleForm_pullback _ _ ((contDiff_actualPair j v).contDiffAt.differentiableAt (by simp))
    (actualPair_denominator_ne_zero x hx hr j v)).symm

def internalParameters (j k : Fin n) (x : ClusterAngularCoordinates i a b S m) : VariableClusterParameters :=
  (x.toFree.base j, (x.toFree.radius, (x.toFree.velocity j, x.toFree.velocity k)))

@[fun_prop] theorem contDiff_internalParameters (j k : Fin n) :
    ContDiff ℝ ⊤ (internalParameters (i := i) (a := a) (b := b) (S := S) (m := m) j k) := by
  unfold internalParameters
  fun_prop

theorem internalPair_eq (j k : Fin n) (hj : j ∈ S) (hk : k ∈ S)
    (x : ClusterAngularCoordinates i a b S m) :
    variableInternalClusterPair (internalParameters j k x) = actualPair j (Sum.inl k) x := by
  change (x.toFree.base j + (x.toFree.radius : ℂ) * x.toFree.velocity j,
    x.toFree.base j + (x.toFree.radius : ℂ) * x.toFree.velocity k) =
      (x.toFree.base j + (x.toFree.radius : ℂ) * x.toFree.velocity j,
        x.toFree.base k + (x.toFree.radius : ℂ) * x.toFree.velocity k)
  rw [x.toFree.base_eq_of_same (Or.inr ⟨hj, hk⟩)]

def internalRatio (j k : Fin n) : ClusterAngularCoordinates i a b S m → ℂ :=
  variableInternalClusterRegularizedRatio ∘ internalParameters j k

def internalEdgeForm (j k : Fin n) (x : ClusterAngularCoordinates i a b S m) :
    ClusterAngularCoordinates i a b S m [⋀^Fin 1]→L[ℝ] ℝ := angularPullback (internalRatio j k) x

theorem velocityDifference_ne_zero (x : ClusterAngularCoordinates i a b S m)
    (hx : x.toFree.OpenConditions) (j k : Fin n) (hj : j ∈ S) (hk : k ∈ S) (hkj : k ≠ j) :
    x.toFree.velocity k - x.toFree.velocity j ≠ 0 :=
  sub_ne_zero.mpr (hx.1.2.2.2.1 k j hkj (Or.inr ⟨hk, hj⟩))

theorem internalDenominator_face_ne_zero (x : ClusterAngularCoordinates i a b S m)
    (hx : x.toFree.OpenConditions) (hr : x.toFree.radius = 0) (j k : Fin n) :
    variableInternalClusterDenominator (internalParameters j k x) ≠ 0 := by
  have hc : 0 < (x.toFree.base j).im := hx.1.2.1 j
  simpa only [internalParameters, variableInternalClusterDenominator, hr, Complex.ofReal_zero,
    zero_mul, add_zero] using harmonicDenominator_ne_zero hc hc.le

/-- Smoothness of the genuinely regularized internal edge in every free chart variable. -/
theorem contDiffAt_internalEdgeForm_face (x : ClusterAngularCoordinates i a b S m)
    (hx : x.toFree.OpenConditions) (hr : x.toFree.radius = 0)
    (j k : Fin n) (hj : j ∈ S) (hk : k ∈ S) (hkj : k ≠ j) :
    ContDiffAt ℝ ⊤ (internalEdgeForm j k) x := by
  have hd := internalDenominator_face_ne_zero x hx hr j k
  have hv := velocityDifference_ne_zero x hx j k hj hk hkj
  apply contDiffAt_angularPullback
  · exact (contDiffAt_variableInternalClusterRegularizedRatio _ hd).comp x
      (contDiff_internalParameters j k).contDiffAt
  · exact div_ne_zero hv hd

theorem extDeriv_internalEdgeForm_face (x : ClusterAngularCoordinates i a b S m)
    (hx : x.toFree.OpenConditions) (hr : x.toFree.radius = 0)
    (j k : Fin n) (hj : j ∈ S) (hk : k ∈ S) (hkj : k ≠ j) :
    extDeriv (internalEdgeForm j k) x = 0 := by
  have hd := internalDenominator_face_ne_zero x hx hr j k
  apply extDeriv_angularPullback
  · exact (contDiffAt_variableInternalClusterRegularizedRatio _ hd).comp x
      (contDiff_internalParameters j k).contDiffAt
  · exact div_ne_zero (velocityDifference_ne_zero x hx j k hj hk hkj) hd

/-- At positive admissible radius the extension is the actual harmonic edge pullback. -/
theorem internalEdgeForm_eq_actual (x : ClusterAngularCoordinates i a b S m)
    (hx : x.toFree.OpenConditions) (hr : 0 < x.toFree.radius)
    (j k : Fin n) (hj : j ∈ S) (hk : k ∈ S) (hkj : k ≠ j) :
    internalEdgeForm j k x = actualEdgeForm j (Sum.inl k) x := by
  have hd : variableInternalClusterDenominator (internalParameters j k x) ≠ 0 := by
    rw [← variableInternalClusterPair_denominator, internalPair_eq j k hj hk]
    exact actualPair_denominator_ne_zero x hx hr.le j (Sum.inl k)
  have hv := velocityDifference_ne_zero x hx j k hj hk hkj
  have heq : (fun y : ClusterAngularCoordinates i a b S m =>
      harmonicRatio (actualPair j (Sum.inl k) y).1 (actualPair j (Sum.inl k) y).2) =
      fun y => (y.toFree.radius : ℂ) * internalRatio j k y := by
    funext y
    rw [← internalPair_eq j k hj hk, harmonicRatio_variableInternalClusterPair_factor]
    rfl
  rw [actualEdgeForm, heq]
  symm
  exact angularPullback_real_mul (fun y : ClusterAngularCoordinates i a b S m => y.toFree.radius)
    (internalRatio j k) x (contDiff_radius.contDiffAt.differentiableAt (by simp))
    (((contDiffAt_variableInternalClusterRegularizedRatio _ hd).comp x
      (contDiff_internalParameters j k).contDiffAt).differentiableAt (by simp)) hr.ne' (div_ne_zero hv hd)

theorem actualPair_face (x : ClusterAngularCoordinates i a b S m) (hr : x.toFree.radius = 0)
    (j : Fin n) (v : Fin n ⊕ Fin m) : actualPair j v x = (x.toFree.base j, x.targetBase v) := by
  cases v <;> simp [actualPair, position, targetBase, hr]

/-- External edges are already smooth across the radial face; both edge orientations are allowed. -/
theorem contDiffAt_externalEdgeForm_face (x : ClusterAngularCoordinates i a b S m)
    (hx : x.toFree.OpenConditions) (hr : x.toFree.radius = 0)
    (j : Fin n) (v : Fin n ⊕ Fin m) (hbase : x.targetBase v ≠ x.toFree.base j) :
    ContDiffAt ℝ ⊤ (actualEdgeForm j v) x := by
  have hd := actualPair_denominator_ne_zero x hx (by rw [hr]) j v
  apply contDiffAt_angularPullback
  · exact (contDiffAt_harmonicRatio _ _ hd).comp x (contDiff_actualPair j v).contDiffAt
  · apply div_ne_zero _ hd
    rw [actualPair_face x hr]
    exact sub_ne_zero.mpr hbase

theorem extDeriv_externalEdgeForm_face (x : ClusterAngularCoordinates i a b S m)
    (hx : x.toFree.OpenConditions) (hr : x.toFree.radius = 0)
    (j : Fin n) (v : Fin n ⊕ Fin m) (hbase : x.targetBase v ≠ x.toFree.base j) :
    extDeriv (actualEdgeForm j v) x = 0 := by
  have hd := actualPair_denominator_ne_zero x hx (by rw [hr]) j v
  apply extDeriv_angularPullback
  · exact (contDiffAt_harmonicRatio _ _ hd).comp x (contDiff_actualPair j v).contDiffAt
  · apply div_ne_zero _ hd
    rw [actualPair_face x hr]
    exact sub_ne_zero.mpr hbase

theorem contDiffAt_externalInteriorEdgeForm_face (x : ClusterAngularCoordinates i a b S m)
    (hx : x.toFree.OpenConditions) (hr : x.toFree.radius = 0) (j k : Fin n)
    (hmask : ¬sameInteriorClusterBase S j k) : ContDiffAt ℝ ⊤ (actualEdgeForm j (Sum.inl k)) x :=
  contDiffAt_externalEdgeForm_face x hx hr j (Sum.inl k)
    (Ne.symm (hx.1.2.2.1 j k hmask))

theorem contDiffAt_boundaryEdgeForm_face (x : ClusterAngularCoordinates i a b S m)
    (hx : x.toFree.OpenConditions) (hr : x.toFree.radius = 0) (j : Fin n) (k : Fin m) :
    ContDiffAt ℝ ⊤ (actualEdgeForm j (Sum.inr k)) x := by
  apply contDiffAt_externalEdgeForm_face x hx hr j (Sum.inr k)
  intro heq
  have him := congrArg Complex.im heq
  have hp : 0 < (x.toFree.base j).im := hx.1.2.1 j
  simp only [targetBase, Complex.ofReal_im] at him
  linarith

/-- The actual smooth extension chosen by the fixed cluster type of the edge. -/
def extendedEdgeForm (j : Fin n) (v : Fin n ⊕ Fin m) :
    ClusterAngularCoordinates i a b S m →
      ClusterAngularCoordinates i a b S m [⋀^Fin 1]→L[ℝ] ℝ :=
  match v with
  | Sum.inl k => if j ∈ S ∧ k ∈ S then internalEdgeForm j k else actualEdgeForm j (Sum.inl k)
  | Sum.inr k => actualEdgeForm j (Sum.inr k)

/-- Every non-loop edge has a smooth form in the actual angular/radial coordinate model. -/
theorem contDiffAt_extendedEdgeForm_face (x : ClusterAngularCoordinates i a b S m)
    (hx : x.toFree.OpenConditions) (hr : x.toFree.radius = 0) (j : Fin n) (v : Fin n ⊕ Fin m)
    (hv : v ≠ Sum.inl j) : ContDiffAt ℝ ⊤ (extendedEdgeForm j v) x := by
  cases v with
  | inl k =>
    have hkj : k ≠ j := fun h => hv (congrArg Sum.inl h)
    by_cases hS : j ∈ S ∧ k ∈ S
    · rw [extendedEdgeForm, if_pos hS]
      exact contDiffAt_internalEdgeForm_face x hx hr j k hS.1 hS.2 hkj
    · rw [extendedEdgeForm, if_neg hS]
      apply contDiffAt_externalInteriorEdgeForm_face x hx hr j k
      rintro (hjk | hjk)
      · exact hkj hjk.symm
      · exact hS hjk
  | inr k => exact contDiffAt_boundaryEdgeForm_face x hx hr j k

/-- On positive admissible scales the smooth extension is precisely the original harmonic pullback. -/
theorem extendedEdgeForm_eq_actual (x : ClusterAngularCoordinates i a b S m)
    (hx : x.toFree.OpenConditions) (hr : 0 < x.toFree.radius) (j : Fin n) (v : Fin n ⊕ Fin m)
    (hv : v ≠ Sum.inl j) : extendedEdgeForm j v x = actualEdgeForm j v x := by
  cases v with
  | inl k =>
    have hkj : k ≠ j := fun h => hv (congrArg Sum.inl h)
    by_cases hS : j ∈ S ∧ k ∈ S
    · rw [extendedEdgeForm, if_pos hS]
      exact internalEdgeForm_eq_actual x hx hr j k hS.1 hS.2 hkj
    · rw [extendedEdgeForm, if_neg hS]
  | inr k => rfl

/-- The actual smooth edge extensions are closed on the simple-cluster face. -/
theorem extDeriv_extendedEdgeForm_face (x : ClusterAngularCoordinates i a b S m)
    (hx : x.toFree.OpenConditions) (hr : x.toFree.radius = 0) (j : Fin n) (v : Fin n ⊕ Fin m)
    (hv : v ≠ Sum.inl j) : extDeriv (extendedEdgeForm j v) x = 0 := by
  cases v with
  | inl k =>
    have hkj : k ≠ j := fun h => hv (congrArg Sum.inl h)
    by_cases hS : j ∈ S ∧ k ∈ S
    · rw [extendedEdgeForm, if_pos hS]
      exact extDeriv_internalEdgeForm_face x hx hr j k hS.1 hS.2 hkj
    · rw [extendedEdgeForm, if_neg hS]
      apply extDeriv_externalEdgeForm_face x hx hr j (Sum.inl k)
      have hmask : ¬sameInteriorClusterBase S j k := by
        rintro (h | h)
        · exact hkj h.symm
        · exact hS h
      exact Ne.symm (hx.1.2.2.1 j k hmask)
  | inr k =>
    apply extDeriv_externalEdgeForm_face x hx hr j (Sum.inr k)
    intro heq
    have him := congrArg Complex.im heq
    have hp : 0 < (x.toFree.base j).im := hx.1.2.1 j
    simp only [targetBase, Complex.ofReal_im] at him
    linarith

end ClusterAngularCoordinates

namespace ClusterAngularDomain

variable {n m : ℕ} {i a b : Fin n} {S : Finset (Fin n)}

/-- The smooth interior coordinate functions are exactly the position entries of the actual chart. -/
theorem toCompactification_interior_position (ha : a ∈ S) (hb : b ∈ S) (hba : b ≠ a)
    (hanchor : i ∈ S → a = i) (x : ClusterAngularDomain i a b S m) (j : Fin n) :
    (toCompactification ha hb hba hanchor x).val.1 (Sum.inl j) =
      (x.val.position j : OnePoint ℂ) := by
  rw [toCompactification, NormalizedInteriorClusterSlice.insertion_position]
  apply congrArg ((↑) : ℂ → OnePoint ℂ)
  simp only [NormalizedInteriorClusterSlice.scaledPosition, toSlice, clusterFreeHomeomorph_apply,
    ClusterFreeDomain.toSlice_base, ClusterFreeDomain.toSlice_velocity, ClusterFreeDomain.toSlice_scale]
  rfl

theorem toCompactification_boundary_position (ha : a ∈ S) (hb : b ∈ S) (hba : b ≠ a)
    (hanchor : i ∈ S → a = i) (x : ClusterAngularDomain i a b S m) (j : Fin m) :
    (toCompactification ha hb hba hanchor x).val.1 (Sum.inr j) =
      ((x.val.2.2.1 j : ℂ) : OnePoint ℂ) := by
  rw [toCompactification, NormalizedInteriorClusterSlice.insertion_boundary]
  simp only [toSlice, clusterFreeHomeomorph_apply, ClusterFreeDomain.toSlice_boundary]
  rfl

end ClusterAngularDomain

end EnvelopingIsomorphism.Deformation.Kontsevich
