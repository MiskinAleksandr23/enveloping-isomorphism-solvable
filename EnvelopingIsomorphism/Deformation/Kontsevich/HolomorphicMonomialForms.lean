import EnvelopingIsomorphism.Deformation.Kontsevich.LogMonomialPrimitiveIntegrability

/-! Holomorphic internal-fiber monomials: the actual angular top product is the
exterior derivative of the logarithmic primitive, and both coefficients are L1.
Complex differentiability is proved for the actual monomials from their units.
These hypotheses concern holomorphic internal fibers; they do not cover general
harmonic propagators with conjugated variables. No cluster integral vanishing is asserted.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.HolomorphicMonomial

open MeasureTheory Set
open scoped BigOperators Topology

variable {I J : Type*} [Fintype J]

/-- Actual complex differentiability, including negative integer exponents. -/
theorem differentiableAt_coordinateMonomial
    (a : I → J → ℤ) (u : I → (J → ℂ) → ℂ) (i : I) (x : J → ℂ)
    (hu : DifferentiableAt ℂ (u i) x) (hx : ∀ ν, x ν ≠ 0) :
    DifferentiableAt ℂ (LogMonomial.coordinateMonomial a u i) x := by
  classical
  have hpow (ν : J) : DifferentiableAt ℂ (fun y : J → ℂ => y ν ^ a i ν) x := by
    have hz : DifferentiableAt ℂ (fun z : ℂ => z ^ a i ν) (x ν) :=
      differentiableAt_zpow.mpr (Or.inl (hx ν))
    exact hz.comp x (ContinuousLinearMap.proj ν : (J → ℂ) →L[ℂ] ℂ).differentiableAt
  have hp (s : Finset J) : DifferentiableAt ℂ (fun y : J → ℂ => ∏ ν ∈ s, y ν ^ a i ν) x := by
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.prod_empty] using (differentiableAt_const (c := (1 : ℂ)))
    | @insert ν s hν ih =>
      simp only [Finset.prod_insert hν]
      exact (hpow ν).mul ih
  exact hu.mul (hp Finset.univ)

/-- The real derivative is the restriction of the actual complex derivative;
no externally supplied complex-linear derivative is assumed. -/
theorem fderiv_real_eq_complex_restrict
    (a : I → J → ℤ) (u : I → (J → ℂ) → ℂ) (i : I) (x : J → ℂ)
    (hu : DifferentiableAt ℂ (u i) x) (hx : ∀ ν, x ν ≠ 0) :
    fderiv ℝ (LogMonomial.coordinateMonomial a u i) x =
      (fderiv ℂ (LogMonomial.coordinateMonomial a u i) x).restrictScalars ℝ :=
  (differentiableAt_coordinateMonomial a u i x hu hx).fderiv_restrictScalars ℝ

variable {n N : ℕ}

/-- The determinant product of actual pulled-back angular forms. -/
def angularTopForm (a : Fin (n + 1) → Fin N → ℤ)
    (u : Fin (n + 1) → AngularRadial.Coordinates N → ℂ) (x : AngularRadial.Coordinates N) :
    AngularRadial.Coordinates N [⋀^Fin (n + 1)]→L[ℝ] ℝ :=
  (coordinateVolume (n + 1)).compContinuousLinearMap (ContinuousLinearMap.pi fun i =>
    (angularLinearCoefficient (LogMonomial.coordinateMonomial a u i x)⁻¹).comp
      (fderiv ℝ (LogMonomial.coordinateMonomial a u i) x))

theorem angularTopForm_apply (a : Fin (n + 1) → Fin N → ℤ)
    (u : Fin (n + 1) → AngularRadial.Coordinates N → ℂ) (x : AngularRadial.Coordinates N)
    (v : Fin (n + 1) → AngularRadial.Coordinates N) :
    angularTopForm a u x v = Matrix.det (fun i j =>
      (fderiv ℝ (LogMonomial.coordinateMonomial a u j) x (v i) /
        LogMonomial.coordinateMonomial a u j x).im) := by
  change Matrix.det (fun i j => ((LogMonomial.coordinateMonomial a u j x)⁻¹ *
    fderiv ℝ (LogMonomial.coordinateMonomial a u j) x (v i)).im) = _
  simp only [div_eq_inv_mul]

/-- The definition is literally the determinant of the existing angular one-form pullbacks. -/
theorem angularTopForm_apply_eq_angularPullbacks (a : Fin (n + 1) → Fin N → ℤ)
    (u : Fin (n + 1) → AngularRadial.Coordinates N → ℂ) (x : AngularRadial.Coordinates N)
    (v : Fin (n + 1) → AngularRadial.Coordinates N) :
    angularTopForm a u x v = Matrix.det (fun i j =>
      ((angularForm (LogMonomial.coordinateMonomial a u j x)).compContinuousLinearMap
        (fderiv ℝ (LogMonomial.coordinateMonomial a u j) x)) (fun _ : Fin 1 => v i)) := by
  simp only [angularTopForm_apply, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    angularForm_apply, Function.comp_apply]

/-- In genuine real top degree, actual holomorphic angular and radial determinants agree
with the positive orientation sign of the coordinatewise `1,I` real basis. -/
theorem angularTopForm_apply_eq_actualRadialDeterminant (hdim : n + 1 = N * 2)
    (a : Fin (n + 1) → Fin N → ℤ)
    (u : Fin (n + 1) → AngularRadial.Coordinates N → ℂ) (x : AngularRadial.Coordinates N)
    (hu : ∀ i, DifferentiableAt ℂ (u i) x) (hx : ∀ ν, x ν ≠ 0)
    (v : Fin (n + 1) → AngularRadial.Coordinates N) :
    angularTopForm a u x v = Matrix.det (LogMonomial.actualRadialMatrix a u v x) := by
  rw [angularTopForm_apply, ← Matrix.det_transpose (LogMonomial.actualRadialMatrix a u v x)]
  change Matrix.det (fun i j =>
    (fderiv ℝ (LogMonomial.coordinateMonomial a u j) x (v i) /
      LogMonomial.coordinateMonomial a u j x).im) = Matrix.det (fun i j =>
    (fderiv ℝ (LogMonomial.coordinateMonomial a u j) x (v i) /
      LogMonomial.coordinateMonomial a u j x).re)
  have heval (i : Fin (n + 1)) (w : AngularRadial.Coordinates N) :
      fderiv ℝ (LogMonomial.coordinateMonomial a u i) x w =
        fderiv ℂ (LogMonomial.coordinateMonomial a u i) x w := by
    rw [fderiv_real_eq_complex_restrict a u i x (hu i) hx]
    rfl
  simp only [heval]
  have h := LogRadialPrimitive.det_im_eq_det_re_of_dimension hdim
    (fun i => (LogMonomial.coordinateMonomial a u i x)⁻¹ •
      (fderiv ℂ (LogMonomial.coordinateMonomial a u i) x).toLinearMap) v
  simpa only [LinearMap.smul_apply, ContinuousLinearMap.coe_coe, smul_eq_mul, div_eq_inv_mul] using h

/-- The actual angular top product is the native exterior derivative of the actual
logarithmic primitive, from C2 complex units and nonzero normal coordinates. -/
theorem angularTopForm_eq_extDeriv_primitive (hdim : n + 1 = N * 2)
    (a : Fin (n + 1) → Fin N → ℤ)
    (u : Fin (n + 1) → AngularRadial.Coordinates N → ℂ) (x : AngularRadial.Coordinates N)
    (hu : ∀ i, ContDiffAt ℂ 2 (u i) x) (hu0 : ∀ i, u i x ≠ 0) (hx : ∀ ν, x ν ≠ 0) :
    angularTopForm a u x = extDeriv (LogRadialPrimitive.primitive (LogMonomial.coordinateMonomial a u)) x := by
  ext v
  rw [angularTopForm_apply_eq_actualRadialDeterminant hdim a u x
    (fun i => (hu i).differentiableAt (by norm_num)) hx,
    LogMonomial.extDeriv_primitive_eq_actualDeterminant_of_C2 a u v x
      (fun i => (hu i).restrict_scalars ℝ) hu0 hx]

/-- The norm bound on actual complex unit derivatives is also the needed real derivative bound. -/
theorem norm_fderiv_real_le {u : AngularRadial.Coordinates N → ℂ} {x : AngularRadial.Coordinates N}
    (hu : DifferentiableAt ℂ u x) {D : ℝ} (hD : ‖fderiv ℂ u x‖ ≤ D) :
    ‖fderiv ℝ u x‖ ≤ D := by
  rw [hu.fderiv_restrictScalars ℝ, ContinuousLinearMap.norm_restrictScalars]
  exact hD

/-- The actual angular top coefficient is genuinely L1 from local C2 complex units.
Upper unit norm bounds are unnecessary for this exterior-derivative coefficient. -/
theorem integrableOn_angularTopCoefficient (hdim : n + 1 = N * 2)
    (a : Fin (n + 1) → Fin N → ℤ)
    (u : Fin (n + 1) → AngularRadial.Coordinates N → ℂ)
    (v : Fin (n + 1) → AngularRadial.Coordinates N) (ε : Fin N → ℝ)
    (U : Set (AngularRadial.Coordinates N)) (hU : IsOpen U)
    (hsub : NormalCrossing.puncturedPolydisc ε ⊆ U)
    (hu : ∀ i, ContDiffOn ℂ 2 (u i) U) (D c : ℝ) (hc : 0 < c)
    (hD : ∀ x ∈ NormalCrossing.puncturedPolydisc ε, ∀ i, ‖fderiv ℂ (u i) x‖ ≤ D)
    (hunit : ∀ x ∈ NormalCrossing.puncturedPolydisc ε, ∀ i, c ≤ ‖u i x‖)
    (hv : ∀ j, ‖v j‖ ≤ 1) :
    IntegrableOn (fun x => angularTopForm a u x v) (NormalCrossing.puncturedPolydisc ε) := by
  have huAt (x : AngularRadial.Coordinates N) (hx : x ∈ NormalCrossing.puncturedPolydisc ε)
      (i : Fin (n + 1)) : ContDiffAt ℂ 2 (u i) x :=
    (hu i).contDiffAt (hU.mem_nhds (hsub hx))
  have hi := LogMonomial.integrableOn_extDeriv_primitiveCoefficient_of_localC2 a u v ε U hU hsub
    (fun i => (hu i).restrict_scalars ℝ) D c hc
    (fun x hx i => norm_fderiv_real_le ((huAt x hx i).differentiableAt (by norm_num)) (hD x hx i))
    hunit hv
  apply hi.congr_fun _ (NormalCrossing.measurableSet_puncturedPolydisc ε)
  intro x hx
  exact congrArg (fun F => F v) (angularTopForm_eq_extDeriv_primitive hdim a u x (huAt x hx)
    (fun i => norm_pos_iff.mp (hc.trans_le (hunit x hx i)))
    (fun ν => norm_pos_iff.mp ((hx ν (mem_univ ν)).1))).symm

/-- Both the actual primitive and the holomorphic angular top coefficient are L1. -/
theorem integrableOn_primitive_and_angularTop (hdim : n + 1 = N * 2)
    (a : Fin (n + 1) → Fin N → ℤ)
    (u : Fin (n + 1) → AngularRadial.Coordinates N → ℂ)
    (v : Fin n → AngularRadial.Coordinates N) (w : Fin (n + 1) → AngularRadial.Coordinates N)
    (ε : Fin N → ℝ) (U : Set (AngularRadial.Coordinates N)) (hU : IsOpen U)
    (hsub : NormalCrossing.puncturedPolydisc ε ⊆ U)
    (hu : ∀ i, ContDiffOn ℂ 2 (u i) U) (D c M : ℝ) (hc : 0 < c)
    (hD : ∀ x ∈ NormalCrossing.puncturedPolydisc ε, ∀ i, ‖fderiv ℂ (u i) x‖ ≤ D)
    (hunit : ∀ x ∈ NormalCrossing.puncturedPolydisc ε, ∀ i, c ≤ ‖u i x‖)
    (hupper : ∀ x ∈ NormalCrossing.puncturedPolydisc ε, ‖u 0 x‖ ≤ M)
    (hv : ∀ j, ‖v j‖ ≤ 1) (hw : ∀ j, ‖w j‖ ≤ 1) :
    IntegrableOn (fun x => LogRadialPrimitive.primitive (LogMonomial.coordinateMonomial a u) x v)
      (NormalCrossing.puncturedPolydisc ε) ∧
    IntegrableOn (fun x => angularTopForm a u x w) (NormalCrossing.puncturedPolydisc ε) := by
  constructor
  · apply LogMonomial.integrableOn_primitiveCoefficient_of_localC1 a u v ε U hU hsub
      (fun i => ((hu i).restrict_scalars ℝ).of_le (by norm_num)) D c M hc
    · intro x hx i
      exact norm_fderiv_real_le (((hu i.succ).contDiffAt (hU.mem_nhds (hsub hx))).differentiableAt
        (by norm_num)) (hD x hx i.succ)
    · exact hunit
    · exact hupper
    · exact hv
  · exact integrableOn_angularTopCoefficient hdim a u w ε U hU hsub hu D c hc hD hunit hw

/-- Every vector of the existing ordered real `1,I` basis has norm one. -/
theorem norm_realBasis (N : ℕ) (i : Fin (N * 2)) : ‖AngularRadial.realBasis N i‖ = 1 := by
  have hb (j : Fin 2) : ‖Complex.basisOneI j‖ = 1 := by
    fin_cases j <;> simp [Complex.coe_basisOneI]
  simp only [AngularRadial.realBasis, Module.Basis.reindex_apply, Pi.basis_apply, Pi.norm_single, hb]

/-- The same ordered real basis, reindexed to the displayed primitive's top degree. -/
def realBasisTuple (hdim : n + 1 = N * 2) : Fin (n + 1) → AngularRadial.Coordinates N :=
  fun i => AngularRadial.realBasis N (finCongr hdim i)

@[simp] theorem norm_realBasisTuple (hdim : n + 1 = N * 2) (i : Fin (n + 1)) :
    ‖realBasisTuple hdim i‖ = 1 := norm_realBasis N _

/-- Actual top density in the native coordinatewise `1,I` real orientation. -/
def angularDensity (hdim : n + 1 = N * 2) (a : Fin (n + 1) → Fin N → ℤ)
    (u : Fin (n + 1) → AngularRadial.Coordinates N → ℂ) (x : AngularRadial.Coordinates N) : ℝ :=
  angularTopForm a u x (realBasisTuple hdim)

theorem angularDensity_eq_extDeriv_primitive (hdim : n + 1 = N * 2)
    (a : Fin (n + 1) → Fin N → ℤ)
    (u : Fin (n + 1) → AngularRadial.Coordinates N → ℂ) (x : AngularRadial.Coordinates N)
    (hu : ∀ i, ContDiffAt ℂ 2 (u i) x) (hu0 : ∀ i, u i x ≠ 0) (hx : ∀ ν, x ν ≠ 0) :
    angularDensity hdim a u x =
      extDeriv (LogRadialPrimitive.primitive (LogMonomial.coordinateMonomial a u)) x (realBasisTuple hdim) :=
  congrArg (fun F => F (realBasisTuple hdim)) (angularTopForm_eq_extDeriv_primitive hdim a u x hu hu0 hx)

/-- Native angular top density is L1 without supplying a basis norm hypothesis. -/
theorem integrableOn_angularDensity (hdim : n + 1 = N * 2)
    (a : Fin (n + 1) → Fin N → ℤ)
    (u : Fin (n + 1) → AngularRadial.Coordinates N → ℂ)
    (ε : Fin N → ℝ) (U : Set (AngularRadial.Coordinates N)) (hU : IsOpen U)
    (hsub : NormalCrossing.puncturedPolydisc ε ⊆ U)
    (hu : ∀ i, ContDiffOn ℂ 2 (u i) U) (D c : ℝ) (hc : 0 < c)
    (hD : ∀ x ∈ NormalCrossing.puncturedPolydisc ε, ∀ i, ‖fderiv ℂ (u i) x‖ ≤ D)
    (hunit : ∀ x ∈ NormalCrossing.puncturedPolydisc ε, ∀ i, c ≤ ‖u i x‖) :
    IntegrableOn (angularDensity hdim a u) (NormalCrossing.puncturedPolydisc ε) :=
  integrableOn_angularTopCoefficient hdim a u (realBasisTuple hdim) ε U hU hsub hu D c hc hD hunit
    (fun i => (norm_realBasisTuple hdim i).le)

end EnvelopingIsomorphism.Deformation.Kontsevich.HolomorphicMonomial
