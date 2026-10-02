import EnvelopingIsomorphism.Deformation.Kontsevich.OneVertexForms
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Actual graph forms in normalized configuration coordinates

The first interior point is fixed at `I`. The remaining interior points and all
boundary points are free coordinates. Ordered edge forms are pullbacks of the
actual harmonic angular form. Their determinant product is evaluated on the
explicit real-coordinate basis, using `1,I` for each complex coordinate.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.GraphForms

open ContinuousAlternatingMap Module

abbrev Coordinates (n m : ℕ) := (Fin n → ℂ) × (Fin m → ℝ)
abbrev Vertex (n m : ℕ) := Fin (n + 1) ⊕ Fin m
abbrev dimension (n m : ℕ) := n * 2 + m

/-- A directed edge with an internal source. No admissibility hypotheses are
needed to define the raw pulled-back form or prove the vanishing result. -/
structure Edge (n m : ℕ) where
  source : Fin (n + 1)
  target : Vertex n m

variable {n m : ℕ}

def interiorPoint (i : Fin (n + 1)) (x : Coordinates n m) : ℂ :=
  Fin.cases Complex.I (fun j => x.1 j) i

@[simp] theorem interiorPoint_zero (x : Coordinates n m) : interiorPoint 0 x = Complex.I := rfl

@[simp] theorem interiorPoint_succ (i : Fin n) (x : Coordinates n m) :
    interiorPoint i.succ x = x.1 i := rfl

def interiorTangent (i : Fin (n + 1)) : Coordinates n m →L[ℝ] ℂ :=
  Fin.cases 0 (fun j => (ContinuousLinearMap.proj j).comp
    (ContinuousLinearMap.fst ℝ (Fin n → ℂ) (Fin m → ℝ))) i

def vertexPoint (v : Vertex n m) (x : Coordinates n m) : ℂ :=
  match v with
  | Sum.inl i => interiorPoint i x
  | Sum.inr j => (x.2 j : ℂ)

def vertexTangent (v : Vertex n m) : Coordinates n m →L[ℝ] ℂ :=
  match v with
  | Sum.inl i => interiorTangent i
  | Sum.inr j => Complex.ofRealCLM.comp ((ContinuousLinearMap.proj j).comp
      (ContinuousLinearMap.snd ℝ (Fin n → ℂ) (Fin m → ℝ)))

theorem hasFDerivAt_interiorPoint (i : Fin (n + 1)) (x : Coordinates n m) :
    HasFDerivAt (interiorPoint (m := m) i) (interiorTangent i) x := by
  cases i using Fin.cases with
  | zero => exact hasFDerivAt_const Complex.I x
  | succ j =>
      exact ((ContinuousLinearMap.proj j).comp
        (ContinuousLinearMap.fst ℝ (Fin n → ℂ) (Fin m → ℝ))).hasFDerivAt

theorem hasFDerivAt_vertexPoint (v : Vertex n m) (x : Coordinates n m) :
    HasFDerivAt (vertexPoint v) (vertexTangent v) x := by
  cases v with
  | inl i => exact hasFDerivAt_interiorPoint i x
  | inr j => exact (vertexTangent (Sum.inr j : Vertex n m)).hasFDerivAt

def edgeMap (e : Edge n m) (x : Coordinates n m) : ℂ × ℂ :=
  (interiorPoint e.source x, vertexPoint e.target x)

def edgeTangent (e : Edge n m) : Coordinates n m →L[ℝ] ℂ × ℂ :=
  (interiorTangent e.source).prod (vertexTangent e.target)

theorem hasFDerivAt_edgeMap (e : Edge n m) (x : Coordinates n m) :
    HasFDerivAt (edgeMap e) (edgeTangent e) x :=
  (hasFDerivAt_interiorPoint e.source x).prodMk (hasFDerivAt_vertexPoint e.target x)

/-- The actual harmonic one-form pulled back along the affine endpoint map. -/
def edgeForm (e : Edge n m) (x : Coordinates n m) :
    Coordinates n m [⋀^Fin 1]→L[ℝ] ℝ :=
  (harmonicAngleForm (edgeMap e x)).compContinuousLinearMap (edgeTangent e)

theorem edgeForm_eq_pullback (e : Edge n m) (x : Coordinates n m) :
    edgeForm e x = (harmonicAngleForm (edgeMap e x)).compContinuousLinearMap
      (fderiv ℝ (edgeMap e) x) := by
  rw [(hasFDerivAt_edgeMap e x).fderiv]
  rfl

def edgeLinear (e : Edge n m) (x : Coordinates n m) : Coordinates n m →L[ℝ] ℝ :=
  (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := Coordinates n m) (F := ℝ)
    (0 : Fin 1)).symm (edgeForm e x)

theorem edgeLinear_apply (e : Edge n m) (x v : Coordinates n m) :
    edgeLinear e x v = edgeForm e x (fun _ : Fin 1 => v) := by
  have h := (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := Coordinates n m)
    (F := ℝ) (0 : Fin 1)).apply_symm_apply (edgeForm e x)
  exact congrArg (fun ω : Coordinates n m [⋀^Fin 1]→L[ℝ] ℝ => ω (fun _ => v)) h

/-- Motion of just the external coordinate `j`. -/
def externalTangent (j : Fin m) : Coordinates n m := (0, Pi.single j 1)

theorem externalTangent_ne_zero (j : Fin m) : externalTangent (n := n) j ≠ 0 := by
  intro h
  have h' := congrArg (fun v : Coordinates n m => v.2 j) h
  simp [externalTangent] at h'

theorem interiorTangent_externalTangent (i : Fin (n + 1)) (j : Fin m) :
    interiorTangent i (externalTangent j) = 0 := by
  cases i using Fin.cases <;> simp [interiorTangent, externalTangent]

theorem vertexTangent_externalTangent (v : Vertex n m) (j : Fin m)
    (hv : v ≠ Sum.inr j) : vertexTangent v (externalTangent j) = 0 := by
  cases v with
  | inl i => exact interiorTangent_externalTangent i j
  | inr l =>
      have hlj : l ≠ j := fun h => hv (congrArg Sum.inr h)
      simp [vertexTangent, externalTangent, hlj]

theorem edgeTangent_externalTangent (e : Edge n m) (j : Fin m)
    (he : e.target ≠ Sum.inr j) : edgeTangent e (externalTangent j) = 0 := by
  apply Prod.ext
  · exact interiorTangent_externalTangent e.source j
  · exact vertexTangent_externalTangent e.target j he

/-- If an external vertex is not an edge's target, its coordinate tangent is
annihilated by that actual pulled-back edge form, at every raw coordinate point. -/
theorem edgeForm_externalTangent (e : Edge n m) (j : Fin m)
    (he : e.target ≠ Sum.inr j) (x : Coordinates n m) :
    edgeForm e x (fun _ : Fin 1 => externalTangent j) = 0 := by
  simp [edgeForm, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    edgeTangent_externalTangent e j he]

theorem edgeLinear_externalTangent (e : Edge n m) (j : Fin m)
    (he : e.target ≠ Sum.inr j) (x : Coordinates n m) :
    edgeLinear e x (externalTangent j) = 0 := by
  rw [edgeLinear_apply]
  exact edgeForm_externalTangent e j he x

theorem exists_nonzero_common_kernel_of_untargeted {r : ℕ}
    (edges : Fin r → Edge n m) (j : Fin m)
    (hj : ∀ a, (edges a).target ≠ Sum.inr j) (x : Coordinates n m) :
    ∃ v : Coordinates n m, v ≠ 0 ∧ ∀ a, edgeLinear (edges a) x v = 0 :=
  ⟨externalTangent j, externalTangent_ne_zero j,
    fun a => edgeLinear_externalTangent (edges a) j (hj a) x⟩

/-- Unflattened real basis: `1,I` in each complex coordinate, followed by the
standard real boundary-coordinate vectors. -/
def splitRealBasis (n m : ℕ) : Basis ((Fin n × Fin 2) ⊕ Fin m) ℝ (Coordinates n m) :=
  ((Pi.basis fun _ : Fin n => Complex.basisOneI).reindex (Equiv.sigmaEquivProd _ _)).prod
    (Pi.basisFun ℝ (Fin m))

/-- Flatten the ordered real/imaginary and boundary labels to consecutive indices. -/
def coordinateIndexEquiv (n m : ℕ) : ((Fin n × Fin 2) ⊕ Fin m) ≃ Fin (dimension n m) :=
  (Equiv.sumCongr finProdFinEquiv (Equiv.refl (Fin m))).trans finSumFinEquiv

def realBasis (n m : ℕ) : Basis (Fin (dimension n m)) ℝ (Coordinates n m) :=
  (splitRealBasis n m).reindex (coordinateIndexEquiv n m)

def externalBasisIndex (n : ℕ) (j : Fin m) : Fin (dimension n m) :=
  coordinateIndexEquiv n m (Sum.inr j)

theorem realBasis_external (j : Fin m) :
    realBasis n m (externalBasisIndex n j) = externalTangent j := by
  simp [realBasis, externalBasisIndex, Basis.reindex_apply, splitRealBasis,
    Basis.prod_apply, Pi.basisFun_apply, externalTangent]

theorem realBasis_internal (i : Fin n) (a : Fin 2) :
    realBasis n m (coordinateIndexEquiv n m (Sum.inl (i, a))) =
      (Pi.single i (Complex.basisOneI a), 0) := by
  simp [realBasis, Basis.reindex_apply, splitRealBasis, Basis.prod_apply, Pi.basis_apply]

/-- Real coordinates in the displayed `1,I`/boundary basis. -/
def realCoordinates (n m : ℕ) : Coordinates n m ≃ₗ[ℝ] (Fin (dimension n m) → ℝ) :=
  (realBasis n m).equivFun

theorem realCoordinates_external (x : Coordinates n m) (j : Fin m) :
    realCoordinates n m x (externalBasisIndex n j) = x.2 j := by
  simp [realCoordinates, Basis.equivFun_apply, realBasis, externalBasisIndex, splitRealBasis]

theorem realCoordinates_internal (x : Coordinates n m) (i : Fin n) (a : Fin 2) :
    realCoordinates n m x (coordinateIndexEquiv n m (Sum.inl (i, a))) =
      (![ (x.1 i).re, (x.1 i).im ] : Fin 2 → ℝ) a := by
  simp [realCoordinates, Basis.equivFun_apply, realBasis, splitRealBasis, Pi.basis_repr]

/-- The determinant product of any ordered finite list of actual edge one-forms. -/
def topForm {r : ℕ} (edges : Fin r → Edge n m) (x : Coordinates n m) :
    Coordinates n m [⋀^Fin r]→L[ℝ] ℝ :=
  (coordinateVolume r).compContinuousLinearMap
    (ContinuousLinearMap.pi fun a => edgeLinear (edges a) x)

theorem topForm_apply {r : ℕ} (edges : Fin r → Edge n m) (x : Coordinates n m)
    (v : Fin r → Coordinates n m) :
    topForm edges x v = Matrix.det
      (fun i j => edgeForm (edges j) x (fun _ : Fin 1 => v i)) := by
  simp only [topForm, ContinuousAlternatingMap.compContinuousLinearMap_apply, coordinateVolume_apply]
  congr 1

/-- Permuting the ordered edges gives the actual determinant orientation sign. -/
theorem topForm_permute {r : ℕ} (edges : Fin r → Edge n m) (σ : Equiv.Perm (Fin r))
    (x : Coordinates n m) :
    topForm (fun a => edges (σ a)) x = (Equiv.Perm.sign σ : ℝ) • topForm edges x := by
  ext v
  rw [topForm_apply]
  change Matrix.det (fun i j => edgeForm (edges (σ j)) x (fun _ : Fin 1 => v i)) =
    (Equiv.Perm.sign σ : ℝ) * topForm edges x v
  rw [topForm_apply]
  exact Matrix.det_permute' σ
    (fun i j => edgeForm (edges j) x (fun _ : Fin 1 => v i))

/-- Top-degree density in the explicit normalized real-coordinate orientation. -/
def topDensity (edges : Fin (dimension n m) → Edge n m) (x : Coordinates n m) : ℝ :=
  topForm edges x (realBasis n m)

theorem topDensity_permute (edges : Fin (dimension n m) → Edge n m)
    (σ : Equiv.Perm (Fin (dimension n m))) (x : Coordinates n m) :
    topDensity (fun a => edges (σ a)) x = (Equiv.Perm.sign σ : ℝ) • topDensity edges x := by
  rw [topDensity, topForm_permute]
  rfl

/-- An external vertex missed by every target gives a zero row of the actual
form-evaluation matrix. Thus the raw top-degree density vanishes identically. -/
theorem topDensity_eq_zero_of_untargeted
    (edges : Fin (dimension n m) → Edge n m) (j : Fin m)
    (hj : ∀ a, (edges a).target ≠ Sum.inr j) (x : Coordinates n m) :
    topDensity edges x = 0 := by
  rw [topDensity, topForm_apply]
  apply Matrix.det_eq_zero_of_row_eq_zero (externalBasisIndex n j)
  intro a
  rw [realBasis_external]
  exact edgeForm_externalTangent (edges a) j (hj a) x

theorem topDensity_eq_zero_of_untargeted_vertex
    (edges : Fin (dimension n m) → Edge n m) (j : Fin m)
    (hj : ∀ a, (edges a).target ≠ Sum.inr j) : topDensity edges = 0 := by
  funext x
  exact topDensity_eq_zero_of_untargeted edges j hj x

/-- The actual integral of an untargeted graph density is zero on every region.
This uses the proved pointwise identity, so it requires no convergence or
integrability assumption and introduces no abstract weight data. -/
theorem integral_topDensity_eq_zero_of_untargeted
    (edges : Fin (dimension n m) → Edge n m) (j : Fin m)
    (hj : ∀ a, (edges a).target ≠ Sum.inr j)
    (s : Set (Coordinates n m)) (μ : MeasureTheory.Measure (Coordinates n m)) :
    (∫ x in s, topDensity edges x ∂μ) = 0 := by
  simp only [topDensity_eq_zero_of_untargeted_vertex edges j hj, Pi.zero_apply,
    MeasureTheory.integral_zero]

end EnvelopingIsomorphism.Deformation.Kontsevich.GraphForms
