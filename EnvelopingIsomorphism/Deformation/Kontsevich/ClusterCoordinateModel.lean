import EnvelopingIsomorphism.Deformation.Kontsevich.ClusterAngularCoordinates

/-! The angular/radial model has a genuine codimension-one linear face and
the standard positive angular orientation. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.ClusterAngularCoordinates

variable {n m : ℕ} {i a b : Fin n} {S : Finset (Fin n)}

def angleProjection : ClusterAngularCoordinates i a b S m →L[ℝ] ℝ where
  toFun x := x.2.2.2.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := by fun_prop

def radiusProjection : ClusterAngularCoordinates i a b S m →L[ℝ] ℝ where
  toFun x := x.2.2.2.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := by fun_prop

abbrev FaceCoordinates (i a b : Fin n) (S : Finset (Fin n)) (m : ℕ) :=
  (ClusterCoarseIndex i a S → ℂ) × (ClusterShapeIndex a b S → ℂ) × (Fin m → ℝ) × ℝ

def splitRadius : ClusterAngularCoordinates i a b S m ≃ₗ[ℝ] FaceCoordinates i a b S m × ℝ where
  toFun x := ((x.1, x.2.1, x.2.2.1, x.2.2.2.1), x.2.2.2.2)
  invFun x := (x.1.1, x.1.2.1, x.1.2.2.1, x.1.2.2.2, x.2)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def faceEmbedding : FaceCoordinates i a b S m →L[ℝ] ClusterAngularCoordinates i a b S m where
  toFun x := (x.1, x.2.1, x.2.2.1, x.2.2.2, 0)
  map_add' _ _ := by simp
  map_smul' _ _ := by simp
  cont := by fun_prop

/-- The scale-zero parameter face is precisely the kernel of the radial coordinate. -/
theorem range_faceEmbedding :
    LinearMap.range (faceEmbedding (i := i) (a := a) (b := b) (S := S) (m := m)).toLinearMap =
      LinearMap.ker radiusProjection.toLinearMap := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    change (0 : ℝ) = 0
    rfl
  · intro hx
    change x.2.2.2.2 = 0 at hx
    refine ⟨(x.1, x.2.1, x.2.2.1, x.2.2.2.1), ?_⟩
    exact Prod.ext rfl (Prod.ext rfl (Prod.ext rfl (Prod.ext rfl hx.symm)))

theorem finrank_face (ha : a ∈ S) (hb : b ∈ S) (hba : b ≠ a) (hanchor : i ∈ S → a = i) :
    Module.finrank ℝ (FaceCoordinates i a b S m) = 2 * n + m - 3 := by
  have h : Module.finrank ℝ (ClusterAngularCoordinates i a b S m) =
      Module.finrank ℝ (FaceCoordinates i a b S m) + 1 := by
    rw [splitRadius.finrank_eq, Module.finrank_prod, Module.finrank_self]
  rw [finrank_eq ha hb hba hanchor] at h
  omega

def referencePhaseParameter (x : ClusterAngularCoordinates i a b S m) : ℂ :=
  circleParameter (angleProjection x)

theorem referencePhaseParameter_eq (x : ClusterAngularCoordinates i a b S m) :
    referencePhaseParameter x = (x.toFree.2.2.2.1 : ℂ) := circleParameter_eq _

/-- The positive angular coordinate has coefficient `+1` in the actual global angular form. -/
theorem angularForm_referencePhaseParameter (x : ClusterAngularCoordinates i a b S m) :
    (angularForm (referencePhaseParameter x)).compContinuousLinearMap
      (fderiv ℝ referencePhaseParameter x) =
        ContinuousAlternatingMap.ofSubsingletonLIE (0 : Fin 1) angleProjection := by
  have hd := (hasFDerivAt_circleParameter (angleProjection x)).comp x angleProjection.hasFDerivAt
  change (angularForm (circleParameter (angleProjection x))).compContinuousLinearMap
    (fderiv ℝ (circleParameter ∘ angleProjection) x) = _
  rw [hd.fderiv]
  ext v
  exact congrArg (fun ω : ℝ [⋀^Fin 1]→L[ℝ] ℝ => ω (fun j => angleProjection (v j)))
    (angularForm_circleParameter (angleProjection x))

end EnvelopingIsomorphism.Deformation.Kontsevich.ClusterAngularCoordinates
