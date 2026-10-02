import EnvelopingIsomorphism.Deformation.Kontsevich.HarmonicAngleForm
import Mathlib.Topology.Instances.Matrix

/-!
# Angular forms in the one-interior-vertex chart

Fixing the interior vertex at `I` leaves real boundary coordinates. Each edge
pulls back to `2/(1+x_j²) dx_j`. The determinant product of these actual forms
has coefficient the product of their densities in the standard orientation.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich

variable {m : ℕ}

/-- The ordered coordinate domain is an open subset of the real boundary-coordinate space. -/
theorem isOpen_orderedBoundaryCoordinates (m : ℕ) :
    IsOpen {x : Fin m → ℝ | StrictMono x} := by
  have heq : {x : Fin m → ℝ | StrictMono x} =
      ⋂ (i : Fin m) (j : Fin m) (_ : i < j), {x : Fin m → ℝ | x i < x j} := by
    ext x
    simp [StrictMono]
  rw [heq]
  apply isOpen_iInter_of_finite
  intro i
  apply isOpen_iInter_of_finite
  intro j
  apply isOpen_iInter_of_finite
  intro h
  exact isOpen_lt (continuous_apply i) (continuous_apply j)

/-- An ordered tuple of real boundary points with its single interior point fixed at `I`. -/
def oneVertexConfiguration (x : Fin m → ℝ) (hx : StrictMono x) : Configuration 1 m where
  interior := fun _ => UpperHalfPlane.I
  boundary := x
  interior_injective := fun _ _ _ => Subsingleton.elim _ _
  boundary_strictMono := hx

/-- The normalized one-vertex model is exactly the strictly ordered real-coordinate domain. -/
def oneVertexNormalizedEquiv (m : ℕ) :
    Configuration.Normalized (0 : Fin 1) m ≃ {x : Fin m → ℝ // StrictMono x} where
  toFun c := ⟨c.val.boundary, c.val.boundary_strictMono⟩
  invFun x := ⟨oneVertexConfiguration x.val x.property, rfl⟩
  left_inv c := by
    apply Subtype.ext
    apply Configuration.ext
    · funext i
      have hi : i = 0 := Subsingleton.elim _ _
      simpa only [oneVertexConfiguration, hi] using c.property.symm
    · rfl
  right_inv _ := rfl

def oneVertexEdgeMap (j : Fin m) (x : Fin m → ℝ) : ℂ × ℂ :=
  normalizedBoundaryTarget (x j)

def oneVertexEdgeTangent (j : Fin m) : (Fin m → ℝ) →L[ℝ] ℂ × ℂ :=
  normalizedBoundaryTangent.comp (ContinuousLinearMap.proj j)

theorem hasFDerivAt_oneVertexEdgeMap (j : Fin m) (x : Fin m → ℝ) :
    HasFDerivAt (oneVertexEdgeMap j) (oneVertexEdgeTangent j) x := by
  have hp : HasFDerivAt (fun y : Fin m → ℝ => y j) (ContinuousLinearMap.proj j) x :=
    (ContinuousLinearMap.proj j : (Fin m → ℝ) →L[ℝ] ℝ).hasFDerivAt
  exact (hasFDerivAt_normalizedBoundaryTarget (x j)).comp x hp

/-- The actual pulled-back form of the edge from the fixed interior vertex to target `j`. -/
def oneVertexEdgeForm (j : Fin m) (x : Fin m → ℝ) :
    (Fin m → ℝ) [⋀^Fin 1]→L[ℝ] ℝ :=
  (harmonicAngleForm (oneVertexEdgeMap j x)).compContinuousLinearMap (oneVertexEdgeTangent j)

theorem oneVertexEdgeForm_apply (j : Fin m) (x : Fin m → ℝ) (v : Fin 1 → Fin m → ℝ) :
    oneVertexEdgeForm j x v = (2 / (1 + (x j) ^ 2)) * v 0 j :=
  harmonicAngleForm_normalized_boundary (x j) (fun i => v i j)

/-- The continuous linear functional underlying an edge form in the normalized chart. -/
def oneVertexEdgeLinear (j : Fin m) (x : Fin m → ℝ) : (Fin m → ℝ) →L[ℝ] ℝ :=
  (2 / (1 + (x j) ^ 2)) • ContinuousLinearMap.proj j

theorem oneVertexEdgeLinear_eq_form (j : Fin m) (x : Fin m → ℝ) :
    ContinuousAlternatingMap.ofSubsingletonLIE (0 : Fin 1) (oneVertexEdgeLinear j x) =
      oneVertexEdgeForm j x := by
  ext v
  rw [oneVertexEdgeForm_apply]
  rfl

/-- The standard determinant volume form on the boundary-coordinate space. -/
def coordinateVolume (m : ℕ) : (Fin m → ℝ) [⋀^Fin m]→L[ℝ] ℝ :=
  { Matrix.detRowAlternating with
    cont := by
      change Continuous (fun M : Matrix (Fin m) (Fin m) ℝ => Matrix.det M)
      exact continuous_id.matrix_det }

@[simp] theorem coordinateVolume_apply (v : Fin m → Fin m → ℝ) :
    coordinateVolume m v = Matrix.det v := rfl

/-- The determinant product of the ordered edge one-forms. -/
def oneVertexTopForm (x : Fin m → ℝ) : (Fin m → ℝ) [⋀^Fin m]→L[ℝ] ℝ :=
  (coordinateVolume m).compContinuousLinearMap
    (ContinuousLinearMap.pi (fun j => oneVertexEdgeLinear j x))

/-- This is the alternating determinant product of the actual pulled-back edge forms. -/
theorem oneVertexTopForm_apply (x : Fin m → ℝ) (v : Fin m → Fin m → ℝ) :
    oneVertexTopForm x v = Matrix.det
      (fun i j => oneVertexEdgeForm j x (fun _ : Fin 1 => v i)) := by
  simp only [oneVertexTopForm, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    coordinateVolume_apply]
  congr 1
  funext i j
  rw [oneVertexEdgeForm_apply]
  rfl

/-- Evaluation on the positively oriented coordinate basis gives precisely the product density. -/
theorem oneVertexTopForm_coordinateBasis (x : Fin m → ℝ) :
    oneVertexTopForm x (fun i => Pi.single i 1) =
      ∏ j : Fin m, (2 / (1 + (x j) ^ 2)) := by
  rw [oneVertexTopForm_apply]
  have hmat : (fun i j : Fin m => oneVertexEdgeForm j x
      (fun _ : Fin 1 => Pi.single i 1)) =
      Matrix.diagonal (fun j : Fin m => 2 / (1 + (x j) ^ 2)) := by
    funext i j
    rw [oneVertexEdgeForm_apply]
    by_cases h : i = j
    · subst j
      simp
    · simp [Matrix.diagonal, h, Ne.symm h]
  rw [hmat, Matrix.det_diagonal]

/-- Reordering outgoing edge labels reorders the actual one-forms in the determinant. -/
def permutedOneVertexTopForm (σ : Equiv.Perm (Fin m)) (x : Fin m → ℝ) :
    (Fin m → ℝ) [⋀^Fin m]→L[ℝ] ℝ :=
  (coordinateVolume m).compContinuousLinearMap
    (ContinuousLinearMap.pi (fun j => oneVertexEdgeLinear (σ j) x))

/-- The geometric sign of an outgoing-edge relabelling is the permutation sign. -/
theorem permutedOneVertexTopForm_eq (σ : Equiv.Perm (Fin m)) (x : Fin m → ℝ) :
    permutedOneVertexTopForm σ x = (Equiv.Perm.sign σ : ℝ) • oneVertexTopForm x := by
  ext v
  change Matrix.det (fun i j => oneVertexEdgeLinear (σ j) x (v i)) =
    (Equiv.Perm.sign σ : ℝ) * Matrix.det (fun i j => oneVertexEdgeLinear j x (v i))
  exact Matrix.det_permute' σ (fun i j => oneVertexEdgeLinear j x (v i))

end EnvelopingIsomorphism.Deformation.Kontsevich
