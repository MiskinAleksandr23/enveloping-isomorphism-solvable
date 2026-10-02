import EnvelopingIsomorphism.Deformation.Kontsevich.BoxStokes
import EnvelopingIsomorphism.Deformation.Kontsevich.CompactSupportBoxes
import EnvelopingIsomorphism.Deformation.Kontsevich.LogCircleNoResidue
import EnvelopingIsomorphism.Deformation.Kontsevich.PolarAnnulusIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-! Stokes across one deleted complex coordinate. The annular identity is obtained
from actual polar pullback and box Stokes; a genuine L1 limit removes the puncture. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Kontsevich.PuncturedCoordinateStokes

open Set MeasureTheory ContinuousAlternatingMap Filter
open BoxStokes
open scoped Topology

abbrev OneForm := ℂ → ℂ [⋀^Fin 1]→L[ℝ] ℝ

def linearForm (ω : OneForm) (z : ℂ) : ℂ →L[ℝ] ℝ :=
  (ContinuousAlternatingMap.ofSubsingletonLIE (0 : Fin 1)).symm (ω z)

@[simp] theorem linearForm_apply (ω : OneForm) (z v : ℂ) :
    linearForm ω z v = ω z (fun _ : Fin 1 ↦ v) := rfl

/-- The positively oriented Cartesian density of the actual exterior derivative. -/
def density (ω : OneForm) (z : ℂ) : ℝ := extDeriv ω z ![1, Complex.I]

/-- Radius is coordinate zero and angle is coordinate one. -/
def polar (x : Coord 2) : ℂ := LogCircle.shrinkingCircle (x 0) (x 1)

def polarDerivative (x : Coord 2) : Coord 2 →L[ℝ] ℂ :=
  circleParameter (x 1) • (Complex.ofRealCLM.comp (ContinuousLinearMap.proj 0)) +
    (polar x * Complex.I) • (Complex.ofRealCLM.comp (ContinuousLinearMap.proj 1))

@[fun_prop] theorem contDiff_polar : ContDiff ℝ ⊤ polar := by
  change ContDiff ℝ ⊤ (fun x : Coord 2 ↦ (x 0 : ℂ) * circleParameter (x 1))
  exact (Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ 0)).mul
    (contDiff_circleParameter.comp (contDiff_apply ℝ ℝ 1))

theorem hasFDerivAt_polar (x : Coord 2) : HasFDerivAt polar (polarDerivative x) x := by
  have hr := Complex.ofRealCLM.hasFDerivAt.comp x (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 ↦ ℝ) 0).hasFDerivAt
  have ht := (hasFDerivAt_circleParameter (x 1)).comp x
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 ↦ ℝ) 1).hasFDerivAt
  have h := hr.mul ht
  convert h using 1 <;> try rfl
  ext v
  simp [polarDerivative, circleParameterTangent, polar, LogCircle.shrinkingCircle, smul_eq_mul]
  ring

@[simp] theorem fderiv_polar (x : Coord 2) : fderiv ℝ polar x = polarDerivative x :=
  (hasFDerivAt_polar x).fderiv

@[simp] theorem polarDerivative_zero (x : Coord 2) :
    polarDerivative x (standardBasis 2 0) = circleParameter (x 1) := by
  simp [polarDerivative, standardBasis]

@[simp] theorem polarDerivative_one (x : Coord 2) :
    polarDerivative x (standardBasis 2 1) = polar x * Complex.I := by
  simp [polarDerivative, standardBasis]

theorem polar_eq_native (x : Coord 2) : polar x = Complex.polarCoord.symm (x 0, x 1) := by
  rw [Complex.polarCoord_symm_apply]
  simp [polar, LogCircle.shrinkingCircle, circleParameter, mul_comm Complex.I,
    Complex.exp_mul_I]

@[simp] theorem norm_polar (x : Coord 2) : ‖polar x‖ = |x 0| := LogCircle.norm_shrinkingCircle _ _

theorem polar_ne_zero {x : Coord 2} (hx : 0 < x 0) : polar x ≠ 0 := by
  apply norm_ne_zero_iff.mp
  rw [norm_polar, abs_of_pos hx]
  exact hx.ne'

def polarPullback (ω : OneForm) : Form 1 :=
  fun x ↦ (ω (polar x)).compContinuousLinearMap (fderiv ℝ polar x)

/-- The actual polar Jacobian is the radius, with positive radius-angle orientation. -/
theorem twoForm_polar_frame (α : ℂ [⋀^Fin 2]→L[ℝ] ℝ) (r θ : ℝ) :
    α ![circleParameter θ, LogCircle.shrinkingCircle r θ * Complex.I] = r * α ![1, Complex.I] := by
  have hn : (circleParameter θ).re * (circleParameter θ).re +
      (circleParameter θ).im * (circleParameter θ).im = 1 := by
    rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq, LogCircle.norm_circleParameter, one_pow]
  change α.toAlternatingMap _ = _
  rw [α.toAlternatingMap.eq_smul_basis_det Complex.basisOneI]
  simp only [AlternatingMap.smul_apply, smul_eq_mul, Module.Basis.det_apply,
    Matrix.det_fin_two, Module.Basis.toMatrix_apply, Complex.coe_basisOneI_repr,
    Matrix.cons_val_zero, Matrix.cons_val_one, Complex.coe_basisOneI,
    LogCircle.shrinkingCircle, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero,
    mul_one]
  calc
    _ = r * ((circleParameter θ).re * (circleParameter θ).re +
      (circleParameter θ).im * (circleParameter θ).im) * α ![1, Complex.I] := by
      change (α ![1, Complex.I]) * _ = _
      ring
    _ = _ := by rw [hn, mul_one]

/-- Exterior differentiation of the actual polar pullback has the actual area Jacobian r. -/
theorem polar_density (ω : OneForm) (x : Coord 2) (hω : DifferentiableAt ℝ ω (polar x)) :
    extDeriv (polarPullback ω) x (standardBasis 2) = x 0 * density ω (polar x) := by
  change extDeriv (fun y ↦ (ω (polar y)).compContinuousLinearMap (fderiv ℝ polar y)) x _ = _
  rw [extDeriv_pullback hω contDiff_polar.contDiffAt (by simp), fderiv_polar,
    ContinuousAlternatingMap.compContinuousLinearMap_apply]
  have hv : ((polarDerivative x : Coord 2 → ℂ) ∘ standardBasis 2) =
      ![circleParameter (x 1), LogCircle.shrinkingCircle (x 0) (x 1) * Complex.I] := by
    funext i
    fin_cases i <;> simp [polar]
  rw [hv]
  exact twoForm_polar_frame (extDeriv ω (polar x)) (x 0) (x 1)

def circleDensity (ω : OneForm) (r θ : ℝ) : ℝ :=
  ω (LogCircle.shrinkingCircle r θ) (fun _ : Fin 1 ↦ LogCircle.shrinkingCircleTangent r θ 1)

/-- The exact circle integral used by the logarithmic no-residue theorem. -/
def circleIntegral (ω : OneForm) (r : ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..(2 * Real.pi), circleDensity ω r θ

theorem circleIntegral_eq_logCircle (ω : OneForm) (r : ℝ) :
    circleIntegral ω r = LogCircle.boundaryIntegral 0 (linearForm ω) r := by
  unfold circleIntegral LogCircle.boundaryIntegral
  congr 1
  funext θ
  simp [LogCircle.logIntegrand, LogCircle.pullback, circleDensity]


/-- A concrete C1 model of the one-form pullback using the native one-form equivalence. -/
theorem polarPullback_eq_linear (ω : OneForm) (x : Coord 2) :
    polarPullback ω x = ContinuousAlternatingMap.ofSubsingletonLIE (0 : Fin 1)
      ((linearForm ω (polar x)).comp (fderiv ℝ polar x)) := by
  apply ContinuousAlternatingMap.ext
  intro v
  change ω (polar x) ((fderiv ℝ polar x) ∘ v) =
    ω (polar x) (fun _ : Fin 1 ↦ fderiv ℝ polar x (v 0))
  congr 1
  funext i
  rw [Subsingleton.elim i 0]
  rfl

theorem contDiffAt_polarPullback (ω : OneForm) (x : Coord 2)
    (hω : ContDiffAt ℝ 1 ω (polar x)) : ContDiffAt ℝ 1 (polarPullback ω) x := by
  have hlin : ContDiffAt ℝ 1 (linearForm ω) (polar x) := by
    change ContDiffAt ℝ 1 ((ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := ℂ) (F := ℝ) (0 : Fin 1)).symm ∘ ω) (polar x)
    exact ((ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := ℂ) (F := ℝ) (0 : Fin 1)).symm.contDiff.contDiffAt).comp _ hω
  have hcomp : ContDiffAt ℝ 1 (fun y ↦ (linearForm ω (polar y)).comp (fderiv ℝ polar y)) x :=
    (hlin.comp x (contDiff_polar.contDiffAt.of_le (by simp))).clm_comp
      (contDiff_polar.contDiffAt.fderiv_right (by simp))
  have h := (ContinuousAlternatingMap.ofSubsingletonLIE (0 : Fin 1)).contDiff.contDiffAt.comp x hcomp
  have heq : polarPullback ω = fun y ↦ ContinuousAlternatingMap.ofSubsingletonLIE (0 : Fin 1)
      ((linearForm ω (polar y)).comp (fderiv ℝ polar y)) := funext (polarPullback_eq_linear ω)
  change ContDiffAt ℝ 1 (fun y ↦ ContinuousAlternatingMap.ofSubsingletonLIE (0 : Fin 1)
    ((linearForm ω (polar y)).comp (fderiv ℝ polar y))) x at h
  rwa [← heq] at h

theorem periodic_circleParameter : Function.Periodic circleParameter (2 * Real.pi) := by
  intro θ
  have h := Complex.exp_mul_I_periodic (θ : ℂ)
  simpa [circleParameter, Complex.ofReal_add, Complex.ofReal_mul, mul_comm Complex.I] using h

theorem periodic_circleDensity (ω : OneForm) (r : ℝ) :
    Function.Periodic (circleDensity ω r) (2 * Real.pi) := by
  intro θ
  simp only [circleDensity, LogCircle.shrinkingCircleTangent_apply, Complex.ofReal_one, mul_one,
    LogCircle.shrinkingCircle, periodic_circleParameter θ]

theorem circleIntegral_eq_centered (ω : OneForm) (r : ℝ) :
    circleIntegral ω r = ∫ θ in (-Real.pi)..Real.pi, circleDensity ω r θ := by
  change (∫ θ in (0 : ℝ)..(2 * Real.pi), circleDensity ω r θ) = _
  have h := (periodic_circleDensity ω r).intervalIntegral_add_eq 0 (-Real.pi)
  simpa only [zero_add, show -Real.pi + 2 * Real.pi = Real.pi by ring] using h

theorem circleParameter_seam : circleParameter (-Real.pi) = circleParameter Real.pi := by
  have h := periodic_circleParameter (-Real.pi)
  rw [show -Real.pi + 2 * Real.pi = Real.pi by ring] at h
  exact h.symm

theorem radial_face_density (ω : OneForm) (r : ℝ) (x : Coord 1) :
    facePullback (polarPullback ω) (0 : Fin 2) r x (standardBasis 1) = circleDensity ω r (x 0) := by
  rw [facePullback_standardBasis]
  change (ω (polar ((0 : Fin 2).insertNth r x))).compContinuousLinearMap
    (fderiv ℝ polar ((0 : Fin 2).insertNth r x)) ((0 : Fin 2).removeNth (standardBasis 2)) = _
  rw [fderiv_polar, ContinuousAlternatingMap.compContinuousLinearMap_apply]
  change ω (LogCircle.shrinkingCircle r (x 0)) _ = _
  congr 1
  funext j
  rw [Subsingleton.elim j 0]
  change polarDerivative _ (standardBasis 2 1) = _
  rw [polarDerivative_one]
  change LogCircle.shrinkingCircle r (x 0) * Complex.I = LogCircle.shrinkingCircleTangent r (x 0) 1
  simp only [LogCircle.shrinkingCircleTangent_apply, Complex.ofReal_one, mul_one]

theorem angular_face_density (ω : OneForm) (θ : ℝ) (x : Coord 1) :
    facePullback (polarPullback ω) (1 : Fin 2) θ x (standardBasis 1) =
      ω (LogCircle.shrinkingCircle (x 0) θ) (fun _ : Fin 1 ↦ circleParameter θ) := by
  rw [facePullback_standardBasis]
  change (ω (polar ((1 : Fin 2).insertNth θ x))).compContinuousLinearMap
    (fderiv ℝ polar ((1 : Fin 2).insertNth θ x)) ((1 : Fin 2).removeNth (standardBasis 2)) = _
  rw [fderiv_polar, ContinuousAlternatingMap.compContinuousLinearMap_apply]
  change ω (LogCircle.shrinkingCircle (x 0) θ) _ = _
  congr 1
  funext j
  rw [Subsingleton.elim j 0]
  change polarDerivative _ (standardBasis 2 0) = _
  rw [polarDerivative_zero]
  rfl

/-- The two seam forms agree as actual pullbacks, so their oriented integrals cancel. -/
theorem angular_seams_equal (ω : OneForm) (x : Coord 1) :
    facePullback (polarPullback ω) (1 : Fin 2) Real.pi x (standardBasis 1) =
      facePullback (polarPullback ω) (1 : Fin 2) (-Real.pi) x (standardBasis 1) := by
  rw [angular_face_density, angular_face_density]
  simp only [LogCircle.shrinkingCircle, circleParameter_seam]

/-- The actual Fin1/real volume-preserving coordinate equivalence. -/
theorem integral_finOne_Icc (a b : Coord 1) (f : Coord 1 → ℝ) :
    (∫ x in Icc a b, f x) = ∫ t in Icc (a 0) (b 0), f (fun _ ↦ t) := by
  convert! (((volume_preserving_funUnique (Fin 1) ℝ).symm _).setIntegral_preimage_emb
    (MeasurableEquiv.measurableEmbedding _) f _).symm
  exact ((OrderIso.funUnique (Fin 1) ℝ).symm.preimage_Icc a b).symm

def polarBox (ε R : ℝ) (h : ε < R) : BoxIntegral.Box (Fin 2) where
  lower := ![ε, -Real.pi]
  upper := ![R, Real.pi]
  lower_lt_upper i := by
    fin_cases i
    · change ε < R
      exact h
    · change -Real.pi < Real.pi
      linarith [Real.pi_pos]

theorem contDiffOn_polarBox (ω : OneForm) (hω : ContDiffOn ℝ 1 ω ({0}ᶜ : Set ℂ))
    (ε R : ℝ) (hε : 0 < ε) (hεR : ε < R) :
    ∀ x ∈ BoxIntegral.Box.Icc (polarBox ε R hεR), ContDiffAt ℝ 1 (polarPullback ω) x := by
  intro x hx
  apply contDiffAt_polarPullback
  apply hω.contDiffAt
  apply isClosed_singleton.isOpen_compl.mem_nhds
  apply polar_ne_zero
  exact hε.trans_le (hx.1 0)

/-- The annular rectangle has exactly the outer circle minus the inner circle as boundary. -/
theorem polar_box_stokes (ω : OneForm) (hω : ContDiffOn ℝ 1 ω ({0}ᶜ : Set ℂ))
    (ε R : ℝ) (hε : 0 < ε) (hεR : ε < R) :
    (∫ x in BoxIntegral.Box.Icc (polarBox ε R hεR), x 0 * density ω (polar x)) =
      circleIntegral ω R - circleIntegral ω ε := by
  have h := BoxStokes.integral_Icc_extDeriv_eq_faces (polarBox ε R hεR) (polarPullback ω)
    (contDiffOn_polarBox ω hω ε R hε hεR)
  have hbody : (∫ x in BoxIntegral.Box.Icc (polarBox ε R hεR),
      extDeriv (polarPullback ω) x (standardBasis 2)) =
      ∫ x in BoxIntegral.Box.Icc (polarBox ε R hεR), x 0 * density ω (polar x) := by
    apply setIntegral_congr_fun (polarBox ε R hεR).isCompact_Icc.measurableSet
    intro x hx
    apply polar_density
    exact (hω.contDiffAt (isClosed_singleton.isOpen_compl.mem_nhds
      (polar_ne_zero (hε.trans_le (hx.1 0))))).differentiableAt (by decide)
  rw [hbody] at h
  let F : Fin 2 → ℝ → ℝ := fun i r ↦
    ∫ x in BoxIntegral.Box.Icc ((polarBox ε R hεR).face i),
      facePullback (polarPullback ω) i r x (standardBasis 1)
  let g : Fin 2 → ℝ := fun i ↦ (-1 : ℝ) ^ i.val •
    (F i ((polarBox ε R hεR).upper i) - F i ((polarBox ε R hεR).lower i))
  have hsum : (∫ x in BoxIntegral.Box.Icc (polarBox ε R hεR), x 0 * density ω (polar x)) = ∑ i, g i := h
  have hh := hsum.trans (Fin.sum_univ_two g)
  have hseam : F 1 Real.pi = F 1 (-Real.pi) := by
    apply setIntegral_congr_fun ((polarBox ε R hεR).face 1).isCompact_Icc.measurableSet
    intro x hx
    exact angular_seams_equal ω x
  have hrad (r : ℝ) : F 0 r = circleIntegral ω r := by
    change (∫ x in Icc _ _, facePullback (polarPullback ω) 0 r x (standardBasis 1)) = _
    simp_rw [radial_face_density]
    rw [integral_finOne_Icc]
    change (∫ θ in Icc (-Real.pi) Real.pi, circleDensity ω r θ) = circleIntegral ω r
    have hle : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
    rw [circleIntegral_eq_centered, intervalIntegral.integral_of_le hle,
      setIntegral_congr_set (Ioc_ae_eq_Icc (α := ℝ) (μ := volume))]
  have hg0 : g 0 = F 0 R - F 0 ε := by
    change (1 : ℝ) • (F 0 R - F 0 ε) = _
    exact one_smul _ _
  have hg1 : g 1 = 0 := by
    change (-1 : ℝ) ^ (1 : ℕ) • (F 1 Real.pi - F 1 (-Real.pi)) = 0
    rw [hseam, sub_self, smul_zero]
  rw [hg0, hg1, add_zero, hrad R, hrad ε] at hh
  exact hh


/-- Genuine Stokes on an annulus, including the positive polar area Jacobian. -/
theorem annulus_stokes (ω : OneForm) (hω : ContDiffOn ℝ 1 ω ({0}ᶜ : Set ℂ))
    (ε R : ℝ) (hε : 0 < ε) (hεR : ε < R) :
    (∫ z in PolarAnnulus.annulus ε R, density ω z) = circleIntegral ω R - circleIntegral ω ε := by
  rw [PolarAnnulus.integral_annulus_eq_closedFinRectangle ε R hε.le]
  have hp : PolarAnnulus.polarFin = polar := funext (fun x ↦ (polar_eq_native x).symm)
  rw [hp]
  exact polar_box_stokes ω hω ε R hε hεR

/-- A circle outside the actual compact support has exactly zero pullback integral. -/
theorem circleIntegral_zero_of_support_bound (ω : OneForm) (R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ z ∈ tsupport ω, ‖z‖ < R) : circleIntegral ω R = 0 := by
  have hz (θ : ℝ) : ω (LogCircle.shrinkingCircle R θ) = 0 := by
    by_contra hn
    have h := hbound _ (subset_tsupport ω hn)
    rw [LogCircle.norm_shrinkingCircle_of_nonneg hR] at h
    exact lt_irrefl _ h
  have heq : circleDensity ω R = 0 := by
    funext θ
    change ω (LogCircle.shrinkingCircle R θ) _ = 0
    rw [hz θ]
    rfl
  rw [circleIntegral, heq]
  simp

theorem density_zero_of_support_bound (ω : OneForm) (R : ℝ)
    (hbound : ∀ z ∈ tsupport ω, ‖z‖ < R) (z : ℂ) (hz : R ≤ ‖z‖) : density ω z = 0 := by
  have hn : z ∉ tsupport ω := fun h ↦ (not_lt_of_ge hz) (hbound z h)
  rw [density, CompactSupportBoxes.extDeriv_zero_of_notMem_tsupport ω hn]
  rfl

/-- Removing one complex puncture by a genuine L1 limit. The boundary hypothesis concerns
 the actual shrinking-circle pullback integral, not a supplied Stokes identity. -/
theorem integral_extDeriv_eq_zero (ω : OneForm) (hω : ContDiffOn ℝ 1 ω ({0}ᶜ : Set ℂ))
    (hcompact : HasCompactSupport ω) (hL1 : Integrable (density ω))
    (hcircle : Tendsto (circleIntegral ω) (𝓝[>] 0) (𝓝 0)) :
    (∫ z : ℂ, density ω z) = 0 := by
  obtain ⟨R, hR, hbound⟩ := hcompact.isCompact.isBounded.exists_pos_norm_lt
  have houter := circleIntegral_zero_of_support_bound ω R hR.le hbound
  have hlimit := PolarAnnulus.tendsto_integral_annulus_of_support R (density ω) hL1
    (density_zero_of_support_bound ω R hbound)
  have heq : (fun ε : ℝ ↦ ∫ z in PolarAnnulus.annulus ε R, density ω z) =ᶠ[𝓝[>] 0]
      (fun ε ↦ -circleIntegral ω ε) := by
    filter_upwards [Ioo_mem_nhdsGT hR] with ε hε
    rw [annulus_stokes ω hω ε R hε.1 hε.2, houter, zero_sub]
  have hz : Tendsto (fun ε : ℝ ↦ -circleIntegral ω ε) (𝓝[>] 0) (𝓝 0) := by
    simpa only [neg_zero] using hcircle.neg
  exact tendsto_nhds_unique hlimit (hz.congr' heq.symm)

/-- The conclusion displayed as the actual native exterior derivative coefficient. -/
theorem integral_extDeriv_standardBasis_eq_zero (ω : OneForm)
    (hω : ContDiffOn ℝ 1 ω ({0}ᶜ : Set ℂ)) (hcompact : HasCompactSupport ω)
    (hL1 : Integrable (fun z ↦ extDeriv ω z ![1, Complex.I]))
    (hcircle : Tendsto (circleIntegral ω) (𝓝[>] 0) (𝓝 0)) :
    (∫ z : ℂ, extDeriv ω z ![1, Complex.I]) = 0 :=
  integral_extDeriv_eq_zero ω hω hcompact hL1 hcircle

end EnvelopingIsomorphism.Deformation.Kontsevich.PuncturedCoordinateStokes
