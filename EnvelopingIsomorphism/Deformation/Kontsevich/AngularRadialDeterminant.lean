import EnvelopingIsomorphism.Deformation.Kontsevich.OneVertexForms
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
The top alternating product of imaginary parts of complex-linear functionals
equals that of their real parts. Both use the same real orientation: `1,I` in
each coordinate of `Fin N → ℂ`. This is the finite-dimensional algebraic step
in the angular/log-radial trick; no analytic vanishing or integrability is asserted.
-/

noncomputable section
namespace EnvelopingIsomorphism.Deformation.Kontsevich.AngularRadial

open Module ContinuousAlternatingMap

abbrev Coordinates (N : ℕ) := Fin N → ℂ
abbrev realDimension (N : ℕ) := N * 2

/-- The ordered real basis uses `1,I` for each complex coordinate. -/
def realBasis (N : ℕ) : Basis (Fin (realDimension N)) ℝ (Coordinates N) :=
  ((Pi.basis fun _ : Fin N => Complex.basisOneI).reindex (Equiv.sigmaEquivProd _ _)).reindex
    finProdFinEquiv

theorem real_finrank (N : ℕ) : Module.finrank ℝ (Coordinates N) = realDimension N := by
  rw [Module.finrank_eq_card_basis (realBasis N), Fintype.card_fin]

/-- Minus the complex structure, as a real continuous linear map. -/
def minusJ (N : ℕ) : Coordinates N →L[ℝ] Coordinates N :=
  ((-Complex.I) • ContinuousLinearMap.id ℂ (Coordinates N)).restrictScalars ℝ

@[simp] theorem minusJ_apply (N : ℕ) (v : Coordinates N) :
    minusJ N v = (-Complex.I) • v := rfl

/-- The real determinant of multiplication by `-I` on one complex coordinate. -/
theorem det_mul_negI : LinearMap.det (LinearMap.mulLeft ℝ (-Complex.I)) = 1 := by
  rw [← LinearMap.det_toMatrix Complex.basisOneI, Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, Complex.coe_basisOneI, Complex.coe_basisOneI_repr]

/-- Applying `-I` independently in each coordinate preserves real orientation.
This includes the zero-dimensional case. -/
theorem det_minusJ (N : ℕ) : LinearMap.det (minusJ N).toLinearMap = 1 := by
  have hmap : (minusJ N).toLinearMap = LinearMap.pi
      (fun i : Fin N => (LinearMap.mulLeft ℝ (-Complex.I)).comp (LinearMap.proj i)) := by
    ext v i
    rfl
  rw [hmap, LinearMap.det_pi]
  simp only [det_mul_negI, Finset.prod_const_one]

variable {N : ℕ}

/-- Real part of an actual complex-linear functional, as a real continuous functional. -/
def reFunctional (ℓ : Coordinates N →ₗ[ℂ] ℂ) : Coordinates N →L[ℝ] ℝ :=
  Complex.reCLM.comp (ℓ.toContinuousLinearMap.restrictScalars ℝ)

/-- Imaginary part of an actual complex-linear functional. -/
def imFunctional (ℓ : Coordinates N →ₗ[ℂ] ℂ) : Coordinates N →L[ℝ] ℝ :=
  Complex.imCLM.comp (ℓ.toContinuousLinearMap.restrictScalars ℝ)

@[simp] theorem reFunctional_apply (ℓ : Coordinates N →ₗ[ℂ] ℂ) (v : Coordinates N) :
    reFunctional ℓ v = (ℓ v).re := rfl

@[simp] theorem imFunctional_apply (ℓ : Coordinates N →ₗ[ℂ] ℂ) (v : Coordinates N) :
    imFunctional ℓ v = (ℓ v).im := rfl

theorem imFunctional_eq_reFunctional_comp_minusJ (ℓ : Coordinates N →ₗ[ℂ] ℂ) :
    imFunctional ℓ = (reFunctional ℓ).comp (minusJ N) := by
  ext v
  change (ℓ v).im = (ℓ ((-Complex.I) • v)).re
  rw [map_smul]
  simp [smul_eq_mul, Complex.mul_re]

/-- Determinant product of the ordered real parts, with actual top degree `2N`. -/
def realTopForm (ℓ : Fin (realDimension N) → Coordinates N →ₗ[ℂ] ℂ) :
    Coordinates N [⋀^Fin (realDimension N)]→L[ℝ] ℝ :=
  (coordinateVolume (realDimension N)).compContinuousLinearMap
    (ContinuousLinearMap.pi fun j => reFunctional (ℓ j))

/-- Determinant product of the ordered imaginary parts, in the same real orientation. -/
def imaginaryTopForm (ℓ : Fin (realDimension N) → Coordinates N →ₗ[ℂ] ℂ) :
    Coordinates N [⋀^Fin (realDimension N)]→L[ℝ] ℝ :=
  (coordinateVolume (realDimension N)).compContinuousLinearMap
    (ContinuousLinearMap.pi fun j => imFunctional (ℓ j))

@[simp] theorem realTopForm_apply
    (ℓ : Fin (realDimension N) → Coordinates N →ₗ[ℂ] ℂ)
    (v : Fin (realDimension N) → Coordinates N) :
    realTopForm ℓ v = Matrix.det (fun i j => (ℓ j (v i)).re) := rfl

@[simp] theorem imaginaryTopForm_apply
    (ℓ : Fin (realDimension N) → Coordinates N →ₗ[ℂ] ℂ)
    (v : Fin (realDimension N) → Coordinates N) :
    imaginaryTopForm ℓ v = Matrix.det (fun i j => (ℓ j (v i)).im) := rfl

/-- Imaginary parts arise by precomposing every real part with the same `-J`. -/
theorem imaginaryTopForm_eq_pullback
    (ℓ : Fin (realDimension N) → Coordinates N →ₗ[ℂ] ℂ) :
    imaginaryTopForm ℓ = (realTopForm ℓ).compContinuousLinearMap (minusJ N) := by
  ext v
  change Matrix.det (fun i j => imFunctional (ℓ j) (v i)) =
    Matrix.det (fun i j => reFunctional (ℓ j) (minusJ N (v i)))
  congr 1
  funext i j
  exact congrArg (fun f : Coordinates N →L[ℝ] ℝ => f (v i))
    (imFunctional_eq_reFunctional_comp_minusJ (ℓ j))

/-- Every actual top real alternating form is invariant under this orientation-preserving `-J`. -/
theorem topForm_pullback_minusJ
    (F : Coordinates N [⋀^Fin (realDimension N)]→L[ℝ] ℝ) :
    F.compContinuousLinearMap (minusJ N) = F := by
  ext v
  change F.toAlternatingMap ((minusJ N).toLinearMap ∘ v) = F.toAlternatingMap v
  rw [F.toAlternatingMap.eq_smul_basis_det (realBasis N)]
  simp only [AlternatingMap.smul_apply, smul_eq_mul, Basis.det_comp, det_minusJ, one_mul]

/-- The finite angular/radial identity with its exact positive sign.
There are `2N` forms on the same `2N`-dimensional real space; no integral occurs. -/
theorem imaginaryTopForm_eq_realTopForm
    (ℓ : Fin (realDimension N) → Coordinates N →ₗ[ℂ] ℂ) :
    imaginaryTopForm ℓ = realTopForm ℓ := by
  rw [imaginaryTopForm_eq_pullback, topForm_pullback_minusJ]

/-- Pointwise determinant form of the same identity on an arbitrary tangent tuple. -/
theorem det_im_eq_det_re
    (ℓ : Fin (realDimension N) → Coordinates N →ₗ[ℂ] ℂ)
    (v : Fin (realDimension N) → Coordinates N) :
    Matrix.det (fun i j => (ℓ j (v i)).im) = Matrix.det (fun i j => (ℓ j (v i)).re) :=
  congrArg (fun F : Coordinates N [⋀^Fin (realDimension N)]→L[ℝ] ℝ => F v)
    (imaginaryTopForm_eq_realTopForm ℓ)

/-- The imaginary functional of a normalized complex differential is exactly
the already-defined angular one-form pulled back by that differential. -/
theorem angularForm_pullback_complexLinear_apply (z : ℂ)
    (f : Coordinates N →ₗ[ℂ] ℂ) (v : Fin 1 → Coordinates N) :
    ((angularForm z).compContinuousLinearMap (f.toContinuousLinearMap.restrictScalars ℝ)) v =
      imFunctional (z⁻¹ • f) (v 0) := by
  rw [ContinuousAlternatingMap.compContinuousLinearMap_apply, angularForm_apply,
    imFunctional_apply]
  change (f (v 0) / z).im = ((z⁻¹ • f) (v 0)).im
  simp [LinearMap.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]

/-- Actual angular pullbacks have the same top determinant as the real
logarithmic coefficients. For the logarithm interpretation the caller also
checks that every z_j is nonzero; this algebraic identity itself holds everywhere. -/
theorem det_angular_pullbacks_eq_re_div
    (z : Fin (realDimension N) → ℂ)
    (f : Fin (realDimension N) → Coordinates N →ₗ[ℂ] ℂ)
    (v : Fin (realDimension N) → Coordinates N) :
    Matrix.det (fun i j =>
      ((angularForm (z j)).compContinuousLinearMap
        ((f j).toContinuousLinearMap.restrictScalars ℝ)) (fun _ : Fin 1 => v i)) =
      Matrix.det (fun i j => (f j (v i) / z j).re) := by
  simp only [angularForm_pullback_complexLinear_apply, imFunctional_apply]
  have h := det_im_eq_det_re (fun j => (z j)⁻¹ • f j) v
  simpa only [LinearMap.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm] using h

end EnvelopingIsomorphism.Deformation.Kontsevich.AngularRadial
