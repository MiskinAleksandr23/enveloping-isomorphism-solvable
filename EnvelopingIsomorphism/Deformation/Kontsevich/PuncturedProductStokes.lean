import EnvelopingIsomorphism.Deformation.Kontsevich.PuncturedCoordinateStokes
import Mathlib.Analysis.Normed.Module.Alternating.Curry
import Mathlib.MeasureTheory.Integral.Prod

/-! Stokes across one deleted complex coordinate with arbitrary passive real coordinates. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Kontsevich.PuncturedProductStokes

open Set MeasureTheory ContinuousAlternatingMap Filter
open BoxStokes
open scoped Topology

abbrev Space (d : ℕ) := ℂ × Coord d
abbrev ProductForm (d : ℕ) := Space d → Space d [⋀^Fin (d + 1)]→L[ℝ] ℝ

/-- The complex real-imaginary orientation followed by the passive standard coordinates. -/
def frame (d : ℕ) : Fin (d + 2) → Space d :=
  Matrix.vecCons (1, 0) (Matrix.vecCons (Complex.I, 0) (fun i ↦ (0, standardBasis d i)))

def density {d : ℕ} (ω : ProductForm d) (p : Space d) : ℝ :=
  extDeriv ω p (frame d)

def headCLM (d : ℕ) : Coord (d + 2) →L[ℝ] Coord 2 :=
  ContinuousLinearMap.pi (fun i ↦ ContinuousLinearMap.proj (i.castLE (by omega)))

def tailCLM (d : ℕ) : Coord (d + 2) →L[ℝ] Coord d :=
  ContinuousLinearMap.pi (fun i ↦ ContinuousLinearMap.proj i.succ.succ)

def polar {d : ℕ} (x : Coord (d + 2)) : Space d :=
  (PuncturedCoordinateStokes.polar (headCLM d x), tailCLM d x)

def polarDerivative {d : ℕ} (x : Coord (d + 2)) : Coord (d + 2) →L[ℝ] Space d :=
  ((PuncturedCoordinateStokes.polarDerivative (headCLM d x)).comp (headCLM d)).prod (tailCLM d)

@[fun_prop] theorem contDiff_polar (d : ℕ) : ContDiff ℝ ⊤ (@polar d) :=
  (PuncturedCoordinateStokes.contDiff_polar.comp (headCLM d).contDiff).prodMk (tailCLM d).contDiff

theorem hasFDerivAt_polar {d : ℕ} (x : Coord (d + 2)) :
    HasFDerivAt polar (polarDerivative x) x :=
  ((PuncturedCoordinateStokes.hasFDerivAt_polar (headCLM d x)).comp x
    (headCLM d).hasFDerivAt).prodMk (tailCLM d).hasFDerivAt

@[simp] theorem fderiv_polar {d : ℕ} (x : Coord (d + 2)) :
    fderiv ℝ polar x = polarDerivative x := (hasFDerivAt_polar x).fderiv

@[simp] theorem polar_fst {d : ℕ} (x : Coord (d + 2)) :
    (polar x).1 = LogCircle.shrinkingCircle (x 0) (x 1) := rfl

@[simp] theorem polar_snd {d : ℕ} (x : Coord (d + 2)) (i : Fin d) :
    (polar x).2 i = x i.succ.succ := rfl

@[simp] theorem castLE_one (d : ℕ) :
    (1 : Fin 2).castLE (show 2 ≤ d + 2 by omega) = 1 := rfl

@[simp] theorem passive_ne_one {d : ℕ} (j : Fin d) : j.succ.succ ≠ (1 : Fin (d + 2)) := by
  intro h
  have hh := congrArg Fin.val h
  change j.val + 1 + 1 = 1 at hh
  omega

@[simp] theorem one_ne_passive {d : ℕ} (j : Fin d) : (1 : Fin (d + 2)) ≠ j.succ.succ := (passive_ne_one j).symm

@[simp] theorem zero_ne_passive {d : ℕ} (j : Fin d) : (0 : Fin (d + 2)) ≠ j.succ.succ :=
  (Fin.succ_ne_zero _).symm

@[simp] theorem polarDerivative_zero {d : ℕ} (x : Coord (d + 2)) :
    polarDerivative x (standardBasis (d + 2) 0) = (circleParameter (x 1), 0) := by
  ext i <;> simp [polarDerivative, headCLM, tailCLM,
    PuncturedCoordinateStokes.polarDerivative, standardBasis, Pi.single_apply]

@[simp] theorem polarDerivative_one {d : ℕ} (x : Coord (d + 2)) :
    polarDerivative x (standardBasis (d + 2) 1) = ((polar x).1 * Complex.I, 0) := by
  ext i <;> simp [polarDerivative, headCLM, tailCLM,
    PuncturedCoordinateStokes.polarDerivative, standardBasis, Pi.single_apply, polar,
    PuncturedCoordinateStokes.polar, LogCircle.shrinkingCircle]

@[simp] theorem polarDerivative_passive {d : ℕ} (x : Coord (d + 2)) (j : Fin d) :
    polarDerivative x (standardBasis (d + 2) j.succ.succ) = (0, standardBasis d j) := by
  ext i <;> simp [polarDerivative, headCLM, tailCLM,
    PuncturedCoordinateStokes.polarDerivative, standardBasis, Pi.single_apply]

/-- The elementary two-column determinant identity, with all passive columns fixed. -/
theorem alternating_two_columns {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {d : ℕ} (α : E [⋀^Fin (d + 2)]→L[ℝ] ℝ) (u v : E) (w : Fin d → E)
    (a b c e : ℝ) :
    α (Matrix.vecCons (a • u + b • v) (Matrix.vecCons (c • u + e • v) w)) =
      (a * e - b * c) * α (Matrix.vecCons u (Matrix.vecCons v w)) := by
  have hzero (t : E) : α (Matrix.vecCons t (Matrix.vecCons t w)) = 0 :=
    α.map_eq_zero_of_eq _ (by simp) Fin.zero_ne_one
  have hswap : α (Matrix.vecCons v (Matrix.vecCons u w)) =
      -α (Matrix.vecCons u (Matrix.vecCons v w)) := by
    have hh := α.toAlternatingMap.map_swap (Matrix.vecCons u (Matrix.vecCons v w)) Fin.zero_ne_one
    change α _ = -α _ at hh
    convert hh using 1
    congr 1
    funext i
    refine Fin.cases ?_ (fun j ↦ Fin.cases ?_ (fun k ↦ ?_) j) i <;>
      simp [Equiv.swap_apply_def]
  change α.curryLeft (a • u + b • v) (Matrix.vecCons (c • u + e • v) w) = _
  simp only [map_add, map_smul, ContinuousAlternatingMap.add_apply,
    ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  change a * (α.curryLeft u).curryLeft (c • u + e • v) w +
    b * (α.curryLeft v).curryLeft (c • u + e • v) w = _
  simp only [map_add, map_smul,
    ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul,
    curryLeft_apply_apply, hzero, hswap]
  ring

theorem complex_pair_decompose (d : ℕ) (z : ℂ) :
    (z, (0 : Coord d)) = z.re • ((1 : ℂ), (0 : Coord d)) + z.im • (Complex.I, (0 : Coord d)) := by
  ext <;> simp

theorem topForm_polar_frame {d : ℕ} (α : Space d [⋀^Fin (d + 2)]→L[ℝ] ℝ)
    (x : Coord (d + 2)) :
    α ((polarDerivative x : Coord (d + 2) → Space d) ∘ standardBasis (d + 2)) =
      x 0 * α (frame d) := by
  have heq : ((polarDerivative x : Coord (d + 2) → Space d) ∘ standardBasis (d + 2)) =
      Matrix.vecCons (circleParameter (x 1), 0)
        (Matrix.vecCons ((polar x).1 * Complex.I, 0) (fun i ↦ (0, standardBasis d i))) := by
    funext i
    refine Fin.cases ?_ (fun j ↦ Fin.cases ?_ (fun k ↦ ?_) j) i <;>
      simp
  rw [heq, complex_pair_decompose d (circleParameter (x 1)),
    complex_pair_decompose d ((polar x).1 * Complex.I), alternating_two_columns]
  have hn : (circleParameter (x 1)).re * (circleParameter (x 1)).re +
      (circleParameter (x 1)).im * (circleParameter (x 1)).im = 1 := by
    rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq, LogCircle.norm_circleParameter, one_pow]
  have hdet : (circleParameter (x 1)).re * ((polar x).1 * Complex.I).im -
      (circleParameter (x 1)).im * ((polar x).1 * Complex.I).re = x 0 := by
    simp only [polar_fst, LogCircle.shrinkingCircle, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, zero_mul, sub_zero, add_zero, mul_one]
    calc
      _ = x 0 * ((circleParameter (x 1)).re * (circleParameter (x 1)).re +
        (circleParameter (x 1)).im * (circleParameter (x 1)).im) := by ring
      _ = x 0 := by rw [hn, mul_one]
  rw [hdet]
  rfl

def polarPullback {d : ℕ} (ω : ProductForm d) : Form (d + 1) :=
  fun x ↦ (ω (polar x)).compContinuousLinearMap (fderiv ℝ polar x)

theorem polar_density {d : ℕ} (ω : ProductForm d) (x : Coord (d + 2))
    (hω : DifferentiableAt ℝ ω (polar x)) :
    extDeriv (polarPullback ω) x (standardBasis (d + 2)) = x 0 * density ω (polar x) := by
  unfold polarPullback
  rw [extDeriv_pullback hω (contDiff_polar d).contDiffAt (by simp), fderiv_polar,
    ContinuousAlternatingMap.compContinuousLinearMap_apply]
  exact topForm_polar_frame (extDeriv ω (polar x)) x

/-- This direct BoxStokes companion needs exactly the differentiability and continuity
used in the genuine box-divergence proof. -/
theorem integral_Icc_extDeriv_eq_faces_of_continuous {n : ℕ}
    (I : BoxIntegral.Box (Fin (n + 1))) (ω : Form n)
    (hω : ∀ x ∈ BoxIntegral.Box.Icc I, DifferentiableAt ℝ ω x)
    (hD : ContinuousOn (fun x ↦ extDeriv ω x (standardBasis (n + 1))) (BoxIntegral.Box.Icc I)) :
    (∫ x in BoxIntegral.Box.Icc I, extDeriv ω x (standardBasis (n + 1))) =
      ∑ i : Fin (n + 1), (-1 : ℝ) ^ i.val •
        ((∫ x in BoxIntegral.Box.Icc (I.face i), facePullback ω i (I.upper i) x (standardBasis n)) -
          ∫ x in BoxIntegral.Box.Icc (I.face i), facePullback ω i (I.lower i) x (standardBasis n)) := by
  have hc : ContinuousOn ω (BoxIntegral.Box.Icc I) :=
    fun x hx ↦ (hω x hx).continuousAt.continuousWithinAt
  simp only [← setIntegral_congr_set (BoxIntegral.Box.coe_ae_eq_Icc _)]
  have hbody := (ContinuousOn.hasBoxIntegral volume hD BoxIntegral.IntegrationParams.GP).integral_eq
  rw [← hbody, ← BoxIntegral.BoxAdditiveMap.volume, BoxStokes.boxIntegral_extDeriv I ω hω]
  unfold BoxStokes.boundaryBoxIntegral
  apply Finset.sum_congr rfl
  intro i hi
  have hu := (ContinuousOn.hasBoxIntegral volume
    (BoxStokes.continuousOn_face_density I ω hc i ⟨I.lower_le_upper i, le_rfl⟩)
    BoxIntegral.IntegrationParams.GP).integral_eq
  have hl := (ContinuousOn.hasBoxIntegral volume
    (BoxStokes.continuousOn_face_density I ω hc i ⟨le_rfl, I.lower_le_upper i⟩)
    BoxIntegral.IntegrationParams.GP).integral_eq
  simp only [BoxIntegral.BoxAdditiveMap.volume]
  rw [hu, hl]

def regularLocus (d : ℕ) : Set (Space d) := {p | p.1 ≠ 0}

theorem isOpen_regularLocus (d : ℕ) : IsOpen (regularLocus d) :=
  isOpen_ne_fun continuous_fst continuous_const

theorem polar_mem_regularLocus {d : ℕ} {x : Coord (d + 2)} (hx : 0 < x 0) :
    polar x ∈ regularLocus d :=
  PuncturedCoordinateStokes.polar_ne_zero (x := headCLM d x) hx

def polarBox (d : ℕ) (ε R : ℝ) (hR : 0 < R) (hεR : ε < R) :
    BoxIntegral.Box (Fin (d + 2)) where
  lower := Matrix.vecCons ε (Matrix.vecCons (-Real.pi) (fun _ ↦ -R))
  upper := Matrix.vecCons R (Matrix.vecCons Real.pi (fun _ ↦ R))
  lower_lt_upper i := by
    refine Fin.cases ?_ (fun j ↦ Fin.cases ?_ (fun k ↦ ?_) j) i
    · exact hεR
    · change -Real.pi < Real.pi
      linarith [Real.pi_pos]
    · change -R < R
      linarith

def cylinder (d : ℕ) (r : ℝ) (x : Coord (d + 1)) : Space d :=
  polar (faceEmbedding 0 r x)

theorem hasFDerivAt_cylinder (d : ℕ) (r : ℝ) (x : Coord (d + 1)) :
    HasFDerivAt (cylinder d r)
      ((polarDerivative (faceEmbedding 0 r x)).comp (faceTangent 0)) x :=
  (hasFDerivAt_polar _).comp x (hasFDerivAt_faceEmbedding 0 r x)

/-- The genuine angular-passive cylinder pullback density, using the actual derivative. -/
def cylinderDensity {d : ℕ} (ω : ProductForm d) (r : ℝ) (x : Coord (d + 1)) : ℝ :=
  (ω (cylinder d r x)).compContinuousLinearMap (fderiv ℝ (cylinder d r) x) (standardBasis (d + 1))

def cylinderStrip (d : ℕ) : Set (Coord (d + 1)) := {x | -Real.pi ≤ x 0 ∧ x 0 ≤ Real.pi}

/-- The circle angle covers a full period and every passive coordinate is integrated. -/
def cylinderIntegral {d : ℕ} (ω : ProductForm d) (r : ℝ) : ℝ :=
  ∫ x in cylinderStrip d, cylinderDensity ω r x

theorem radial_face_density {d : ℕ} (ω : ProductForm d) (r : ℝ) (x : Coord (d + 1)) :
    facePullback (polarPullback ω) 0 r x (standardBasis (d + 1)) = cylinderDensity ω r x := by
  rw [cylinderDensity, (hasFDerivAt_cylinder d r x).fderiv]
  simp only [facePullback, polarPullback, fderiv_faceEmbedding, fderiv_polar,
    ContinuousAlternatingMap.compContinuousLinearMap_apply, cylinder]
  rfl

theorem insert_angle {d : ℕ} (θ : ℝ) (x : Coord (d + 1)) :
    (1 : Fin (d + 2)).insertNth θ x =
      Matrix.vecCons (x 0) (Matrix.vecCons θ (Fin.tail x)) := by
  conv_lhs => rw [← Fin.cons_self_tail x]
  exact (Fin.insertNth_succ_cons 0 θ (x 0) (Fin.tail x)).trans
    (congrArg (fun y : Coord (d + 1) ↦ Matrix.vecCons (x 0) y) (Fin.insertNth_zero' θ (Fin.tail x)))

theorem angular_seams_equal {d : ℕ} (ω : ProductForm d) (x : Coord (d + 1)) :
    facePullback (polarPullback ω) 1 Real.pi x (standardBasis (d + 1)) =
      facePullback (polarPullback ω) 1 (-Real.pi) x (standardBasis (d + 1)) := by
  have hp : polar (faceEmbedding 1 Real.pi x) = polar (faceEmbedding 1 (-Real.pi) x) := by
    ext i <;> simp [polar, PuncturedCoordinateStokes.polar, LogCircle.shrinkingCircle,
      faceEmbedding, insert_angle, headCLM, tailCLM, PuncturedCoordinateStokes.circleParameter_seam]
  have hD : polarDerivative (faceEmbedding 1 Real.pi x) =
      polarDerivative (faceEmbedding 1 (-Real.pi) x) := by
    ext v i <;> simp [polarDerivative, PuncturedCoordinateStokes.polarDerivative,
      PuncturedCoordinateStokes.polar, LogCircle.shrinkingCircle, faceEmbedding,
      insert_angle, headCLM, tailCLM, PuncturedCoordinateStokes.circleParameter_seam]
  simp only [facePullback, polarPullback, fderiv_polar, fderiv_faceEmbedding, hp, hD]

theorem differentiableAt_polarPullback {d : ℕ} (ω : ProductForm d) (x : Coord (d + 2))
    (hω : ContDiffAt ℝ 1 ω (polar x)) : DifferentiableAt ℝ (polarPullback ω) x := by
  apply DifferentiableAt.continuousAlternatingMapCompContinuousLinearMap
    ((hω.differentiableAt (by decide)).comp x (hasFDerivAt_polar x).differentiableAt)
  have hD : ContDiffAt ℝ 1 (fderiv ℝ (@polar d)) x :=
    (contDiff_polar d).contDiffAt.fderiv_right (by simp)
  exact hD.differentiableAt (by decide)

theorem continuousAt_density {d : ℕ} (ω : ProductForm d) (p : Space d)
    (hω : ContDiffAt ℝ 1 ω p) : ContinuousAt (density ω) p :=
  (ContinuousAlternatingMap.apply ℝ _ ℝ (frame d)).continuous.continuousAt.comp
    ((ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ _ ℝ).continuous.continuousAt.comp
      (hω.continuousAt_fderiv (by decide)))

theorem polar_box_stokes_all_faces {d : ℕ} (ω : ProductForm d)
    (hω : ContDiffOn ℝ 1 ω (regularLocus d)) (ε R : ℝ) (hε : 0 < ε) (hεR : ε < R) :
    (∫ x in BoxIntegral.Box.Icc (polarBox d ε R (hε.trans hεR) hεR),
        x 0 * density ω (polar x)) =
      ∑ i : Fin (d + 2), (-1 : ℝ) ^ i.val •
        ((∫ x in BoxIntegral.Box.Icc ((polarBox d ε R (hε.trans hεR) hεR).face i),
            facePullback (polarPullback ω) i ((polarBox d ε R (hε.trans hεR) hεR).upper i) x
              (standardBasis (d + 1))) -
          ∫ x in BoxIntegral.Box.Icc ((polarBox d ε R (hε.trans hεR) hεR).face i),
            facePullback (polarPullback ω) i ((polarBox d ε R (hε.trans hεR) hεR).lower i) x
              (standardBasis (d + 1))) := by
  let I := polarBox d ε R (hε.trans hεR) hεR
  have hc (x : Coord (d + 2)) (hx : x ∈ BoxIntegral.Box.Icc I) :
      ContDiffAt ℝ 1 ω (polar x) :=
    hω.contDiffAt ((isOpen_regularLocus d).mem_nhds
      (polar_mem_regularLocus (hε.trans_le (hx.1 0))))
  have hd : EqOn (fun x ↦ extDeriv (polarPullback ω) x (standardBasis (d + 2)))
      (fun x ↦ x 0 * density ω (polar x)) (BoxIntegral.Box.Icc I) :=
    fun x hx ↦ polar_density ω x ((hc x hx).differentiableAt (by decide))
  rw [← setIntegral_congr_fun I.isCompact_Icc.measurableSet hd]
  apply integral_Icc_extDeriv_eq_faces_of_continuous
  · exact fun x hx ↦ differentiableAt_polarPullback ω x (hc x hx)
  · apply ContinuousOn.congr _ hd
    intro x hx
    exact ((continuous_apply 0).continuousAt.mul
      ((continuousAt_density ω (polar x) (hc x hx)).comp
        (contDiff_polar d).continuous.continuousAt)).continuousWithinAt

/-- Both complex radius and every passive coordinate are strictly bounded on support. -/
def SupportBound {d : ℕ} (ω : ProductForm d) (R : ℝ) : Prop :=
  ∀ p ∈ tsupport ω, ‖p.1‖ < R ∧ ∀ j, |p.2 j| < R

theorem exists_supportBound {d : ℕ} (ω : ProductForm d) (hω : HasCompactSupport ω) :
    ∃ R : ℝ, 0 < R ∧ SupportBound ω R := by
  obtain ⟨R, hR, hb⟩ := hω.isCompact.isBounded.exists_pos_norm_lt
  refine ⟨R, hR, fun p hp ↦ ⟨?_, fun j ↦ ?_⟩⟩
  · exact (le_max_left ‖p.1‖ ‖p.2‖).trans_lt (hb p hp)
  · have hj : |p.2 j| ≤ ‖p.2‖ := by simpa using norm_le_pi_norm p.2 j
    exact (hj.trans (le_max_right ‖p.1‖ ‖p.2‖)).trans_lt (hb p hp)

theorem zero_of_radius_ge {d : ℕ} (ω : ProductForm d) {R : ℝ} (hbound : SupportBound ω R)
    (p : Space d) (hp : R ≤ ‖p.1‖) : ω p = 0 :=
  image_eq_zero_of_notMem_tsupport (fun h ↦ (not_lt_of_ge hp) (hbound p h).1)

theorem zero_of_passive_ge {d : ℕ} (ω : ProductForm d) {R : ℝ} (hbound : SupportBound ω R)
    (p : Space d) (j : Fin d) (hp : R ≤ |p.2 j|) : ω p = 0 :=
  image_eq_zero_of_notMem_tsupport (fun h ↦ (not_lt_of_ge hp) ((hbound p h).2 j))

theorem passive_face_zero {d : ℕ} (ω : ProductForm d) {R c : ℝ}
    (hbound : SupportBound ω R) (j : Fin d) (hc : R ≤ |c|) (x : Coord (d + 1)) :
    facePullback (polarPullback ω) j.succ.succ c x (standardBasis (d + 1)) = 0 := by
  have hz : ω (polar (faceEmbedding j.succ.succ c x)) = 0 := by
    apply zero_of_passive_ge ω hbound _ j
    simpa only [polar_snd, faceEmbedding, Fin.insertNth_apply_same] using hc
  simp only [facePullback, polarPullback, hz]
  rfl

theorem outer_face_zero {d : ℕ} (ω : ProductForm d) {R : ℝ} (hR : 0 ≤ R)
    (hbound : SupportBound ω R) (x : Coord (d + 1)) :
    facePullback (polarPullback ω) 0 R x (standardBasis (d + 1)) = 0 := by
  have hz : ω (polar (faceEmbedding 0 R x)) = 0 := by
    apply zero_of_radius_ge ω hbound
    simp only [polar_fst, LogCircle.norm_shrinkingCircle, faceEmbedding,
      Fin.insertNth_apply_same, abs_of_nonneg hR, le_refl]
  simp only [facePullback, polarPullback, hz]
  rfl

theorem cylinderDensity_zero_of_passive_ge {d : ℕ} (ω : ProductForm d) {R : ℝ}
    (hbound : SupportBound ω R) (r : ℝ) (x : Coord (d + 1)) (j : Fin d)
    (hx : R ≤ |x j.succ|) : cylinderDensity ω r x = 0 := by
  have hz : ω (cylinder d r x) = 0 := by
    apply zero_of_passive_ge ω hbound _ j
    simpa [cylinder, polar_snd, faceEmbedding, Fin.insertNth_zero'] using hx
  simp only [cylinderDensity, hz]
  rfl

theorem cylinderIntegral_eq_radial_face {d : ℕ} (ω : ProductForm d) {R : ℝ}
    (hbound : SupportBound ω R) (ε r : ℝ) (hR : 0 < R) (hεR : ε < R) :
    cylinderIntegral ω r =
      ∫ x in BoxIntegral.Box.Icc ((polarBox d ε R hR hεR).face 0),
        facePullback (polarPullback ω) 0 r x (standardBasis (d + 1)) := by
  simp_rw [radial_face_density]
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    ((measurableSet_le measurable_const (measurable_pi_apply 0)).inter
      (measurableSet_le (measurable_pi_apply 0) measurable_const))
  · intro x hx
    exact ⟨hx.1 0, hx.2 0⟩
  · rintro x ⟨hx, hn⟩
    by_contra hz
    have hb (j : Fin d) : |x j.succ| < R :=
      lt_of_not_ge (fun hj ↦ hz (cylinderDensity_zero_of_passive_ge ω hbound r x j hj))
    apply hn
    constructor
    · intro i
      refine Fin.cases hx.1 (fun j ↦ ?_) i
      exact (abs_lt.mp (hb j)).1.le
    · intro i
      refine Fin.cases hx.2 (fun j ↦ ?_) i
      exact (abs_lt.mp (hb j)).2.le

/-- Actual polar BoxStokes after cancellation: all artificial faces disappear,
and the inner cylinder has the negative radial-face orientation. -/
theorem polar_box_stokes {d : ℕ} (ω : ProductForm d)
    (hω : ContDiffOn ℝ 1 ω (regularLocus d)) {R : ℝ} (hbound : SupportBound ω R)
    (ε : ℝ) (hε : 0 < ε) (hεR : ε < R) :
    (∫ x in BoxIntegral.Box.Icc (polarBox d ε R (hε.trans hεR) hεR),
      x 0 * density ω (polar x)) = -cylinderIntegral ω ε := by
  rw [polar_box_stokes_all_faces ω hω ε R hε hεR]
  let I := polarBox d ε R (hε.trans hεR) hεR
  let F : Fin (d + 2) → ℝ → ℝ := fun i r ↦
    ∫ x in BoxIntegral.Box.Icc (I.face i),
      facePullback (polarPullback ω) i r x (standardBasis (d + 1))
  change (∑ i : Fin (d + 2), (-1 : ℝ) ^ i.val • (F i (I.upper i) - F i (I.lower i))) = _
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  have hs : F 1 Real.pi = F 1 (-Real.pi) := by
    apply setIntegral_congr_fun (I.face 1).isCompact_Icc.measurableSet
    exact fun x _ ↦ angular_seams_equal ω x
  have ho : F 0 R = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    exact fun x _ ↦ outer_face_zero ω (hε.trans hεR).le hbound x
  have hp (j : Fin d) : F j.succ.succ R = 0 ∧ F j.succ.succ (-R) = 0 := by
    constructor <;> apply setIntegral_eq_zero_of_forall_eq_zero <;> intro x _
    · exact passive_face_zero ω hbound j (le_abs_self R) x
    · exact passive_face_zero ω hbound j (by simpa using le_abs_self R) x
  change (1 : ℝ) • (F 0 R - F 0 ε) +
    ((-1 : ℝ) ^ 1 • (F 1 Real.pi - F 1 (-Real.pi)) +
      ∑ j : Fin d, (-1 : ℝ) ^ j.succ.succ.val • (F j.succ.succ R - F j.succ.succ (-R))) = _
  simp only [hs, ho, hp, sub_self, smul_zero, Finset.sum_const_zero, add_zero, one_smul, zero_sub]
  congr 1
  exact (cylinderIntegral_eq_radial_face ω hbound ε ε (hε.trans hεR) hεR).symm

def split (d : ℕ) : Coord (d + 2) ≃ᵐ Coord 2 × Coord d :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 2) ↦ ℝ) 0).trans
    (((MeasurableEquiv.refl ℝ).prodCongr
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) ↦ ℝ) 0)).trans
      (MeasurableEquiv.prodAssoc.symm.trans
        (MeasurableEquiv.finTwoArrow.symm.prodCongr (MeasurableEquiv.refl (Coord d)))))

theorem volume_preserving_split (d : ℕ) : MeasurePreserving (split d) := by
  exact (((volume_preserving_finTwoArrow ℝ).symm _).prod (MeasurePreserving.id _)).comp
    ((volume_preserving_prodAssoc.symm _).comp
      (((MeasurePreserving.id _).prod
        (volume_preserving_piFinSuccAbove (fun _ : Fin (d + 1) ↦ ℝ) 0)).comp
        (volume_preserving_piFinSuccAbove (fun _ : Fin (d + 2) ↦ ℝ) 0)))

theorem split_apply (d : ℕ) (x : Coord (d + 2)) :
    split d x = (![x 0, x 1], fun j ↦ x j.succ.succ) := by
  rfl

@[simp] theorem split_fst_zero (d : ℕ) (x : Coord (d + 2)) : (split d x).1 0 = x 0 := by
  rw [split_apply]
  rfl

theorem split_symm_apply (d : ℕ) (p : Coord 2 × Coord d) :
    (split d).symm p = Matrix.vecCons (p.1 0) (Matrix.vecCons (p.1 1) p.2) := by
  apply (split d).injective
  rw [(split d).apply_symm_apply, split_apply]
  apply Prod.ext
  · ext i
    fin_cases i <;> rfl
  · rfl

theorem polar_eq_split {d : ℕ} (x : Coord (d + 2)) :
    polar x = (PolarAnnulus.polarFin ((split d x).1), (split d x).2) :=
  Prod.ext (PuncturedCoordinateStokes.polar_eq_native (headCLM d x)) rfl

def passiveBox (d : ℕ) (R : ℝ) : Set (Coord d) := Icc (fun _ ↦ -R) (fun _ ↦ R)

theorem split_preimage_rectangle (d : ℕ) (ε R : ℝ) (hR : 0 < R) (hεR : ε < R) :
    split d ⁻¹' (Icc ![ε, -Real.pi] ![R, Real.pi] ×ˢ passiveBox d R) =
      BoxIntegral.Box.Icc (polarBox d ε R hR hεR) := by
  ext x
  change ((split d x).1 ∈ Icc ![ε, -Real.pi] ![R, Real.pi] ∧
    (split d x).2 ∈ passiveBox d R) ↔
      (Matrix.vecCons ε (Matrix.vecCons (-Real.pi) (fun _ ↦ -R)) ≤ x ∧
       x ≤ Matrix.vecCons R (Matrix.vecCons Real.pi (fun _ ↦ R)))
  simp only [split_apply, mem_Icc, passiveBox, Pi.le_def]
  simp only [Fin.forall_fin_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.forall_fin_zero, and_true]
  tauto

theorem integral_box_eq_product (d : ℕ) (ε R : ℝ) (hR : 0 < R) (hεR : ε < R)
    (f : Space d → ℝ) :
    (∫ x in BoxIntegral.Box.Icc (polarBox d ε R hR hεR), x 0 * f (polar x)) =
      ∫ p in Icc ![ε, -Real.pi] ![R, Real.pi] ×ˢ passiveBox d R,
        p.1 0 * f (PolarAnnulus.polarFin p.1, p.2) := by
  have h := (volume_preserving_split d).setIntegral_preimage_emb
    (split d).measurableEmbedding
    (fun p : Coord 2 × Coord d ↦ p.1 0 * f (PolarAnnulus.polarFin p.1, p.2))
    (Icc ![ε, -Real.pi] ![R, Real.pi] ×ˢ passiveBox d R)
  rw [split_preimage_rectangle d ε R hR hεR] at h
  simpa only [← polar_eq_split, split_fst_zero] using h

theorem setIntegral_prod_symm {A B : Type*} [MeasureSpace A] [MeasureSpace B] [SigmaFinite (volume : Measure A)]
    [SigmaFinite (volume : Measure B)] (f : A × B → ℝ) (s : Set A) (t : Set B)
    (hf : IntegrableOn f (s ×ˢ t)) :
    (∫ p in s ×ˢ t, f p) = ∫ y in t, ∫ x in s, f (x, y) := by
  simp only [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at hf ⊢
  exact integral_prod_symm f hf

/-- Product change of variables is proved by genuine Fubini and the native complex
polar theorem. The second integrability input is independently obtained from C¹
regularity on the actual polar box in the Stokes consumer. -/
theorem integral_annulus_product_eq_box {d : ℕ} (f : Space d → ℝ)
    (hf : Integrable f) (ε R : ℝ) (hε : 0 < ε) (hεR : ε < R)
    (hbox : IntegrableOn (fun x ↦ x 0 * f (polar x))
      (BoxIntegral.Box.Icc (polarBox d ε R (hε.trans hεR) hεR))) :
    (∫ p in PolarAnnulus.annulus ε R ×ˢ passiveBox d R, f p) =
      ∫ x in BoxIntegral.Box.Icc (polarBox d ε R (hε.trans hεR) hεR), x 0 * f (polar x) := by
  rw [setIntegral_prod_symm f _ _ hf.integrableOn, integral_box_eq_product]
  let g : Coord 2 × Coord d → ℝ := fun p ↦ p.1 0 * f (PolarAnnulus.polarFin p.1, p.2)
  have hg : IntegrableOn g (Icc ![ε, -Real.pi] ![R, Real.pi] ×ˢ passiveBox d R) := by
    rw [← (volume_preserving_split d).integrableOn_comp_preimage (split d).measurableEmbedding,
      split_preimage_rectangle d ε R (hε.trans hεR) hεR]
    simpa only [Function.comp_def, g, ← polar_eq_split, split_fst_zero] using hbox

  rw [setIntegral_prod_symm g _ _ hg]
  apply setIntegral_congr_fun measurableSet_Icc
  intro y hy
  exact PolarAnnulus.integral_annulus_eq_closedFinRectangle ε R hε.le (fun z ↦ f (z, y))

theorem integrableOn_polar_density {d : ℕ} (ω : ProductForm d)
    (hω : ContDiffOn ℝ 1 ω (regularLocus d)) (ε R : ℝ) (hε : 0 < ε) (hεR : ε < R) :
    IntegrableOn (fun x ↦ x 0 * density ω (polar x))
      (BoxIntegral.Box.Icc (polarBox d ε R (hε.trans hεR) hεR)) := by
  refine (show ContinuousOn (fun x ↦ x 0 * density ω (polar x))
    (BoxIntegral.Box.Icc (polarBox d ε R (hε.trans hεR) hεR)) from ?_).integrableOn_compact
      (polarBox d ε R (hε.trans hεR) hεR).isCompact_Icc
  intro x hx
  have hc : ContDiffAt ℝ 1 ω (polar x) :=
    hω.contDiffAt ((isOpen_regularLocus d).mem_nhds
      (polar_mem_regularLocus (hε.trans_le (hx.1 0))))
  exact ((continuous_apply 0).continuousAt.mul
    ((continuousAt_density ω (polar x) hc).comp
      (contDiff_polar d).continuous.continuousAt)).continuousWithinAt

/-- Genuine cylindrical annulus Stokes for compactly supported forms. -/
theorem annulus_product_stokes {d : ℕ} (ω : ProductForm d)
    (hω : ContDiffOn ℝ 1 ω (regularLocus d)) (hL1 : Integrable (density ω))
    {R : ℝ} (hbound : SupportBound ω R) (ε : ℝ) (hε : 0 < ε) (hεR : ε < R) :
    (∫ p in PolarAnnulus.annulus ε R ×ˢ passiveBox d R, density ω p) =
      -cylinderIntegral ω ε := by
  rw [integral_annulus_product_eq_box (density ω) hL1 ε R hε hεR
    (integrableOn_polar_density ω hω ε R hε hεR)]
  exact polar_box_stokes ω hω hbound ε hε hεR

def innerCutoff {d : ℕ} (ε : ℝ) (f : Space d → ℝ) : Space d → ℝ :=
  {p : Space d | ε < ‖p.1‖}.indicator f

theorem measurableSet_innerCutoff (d : ℕ) (ε : ℝ) :
    MeasurableSet {p : Space d | ε < ‖p.1‖} :=
  (isOpen_lt continuous_const continuous_fst.norm).measurableSet

theorem ae_mem_regularLocus (d : ℕ) : ∀ᵐ p : Space d, p ∈ regularLocus d := by
  rw [Measure.volume_eq_prod]
  apply (Measure.ae_prod_iff_ae_ae (isOpen_regularLocus d).measurableSet).mpr
  have hz : ∀ᵐ z : ℂ, z ≠ 0 := by simp [ae_iff]
  filter_upwards [hz] with z hz
  exact Filter.Eventually.of_forall (fun _ ↦ hz)

theorem tendsto_innerCutoff_value {d : ℕ} (f : Space d → ℝ) (p : Space d)
    (hp : p ∈ regularLocus d) :
    Tendsto (fun ε : ℝ ↦ innerCutoff ε f p) (𝓝[>] 0) (𝓝 (f p)) := by
  have he : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε < ‖p.1‖ :=
    (show ∀ᶠ ε : ℝ in 𝓝 0, ε < ‖p.1‖ from Iio_mem_nhds (norm_pos_iff.mpr hp)).filter_mono
      nhdsWithin_le_nhds
  apply tendsto_const_nhds.congr'
  filter_upwards [he] with ε hε
  exact (Set.indicator_of_mem (show p ∈ {q : Space d | ε < ‖q.1‖} from hε) f).symm

/-- The genuine L¹ cutoff convergence on the whole product space. -/
theorem tendsto_innerCutoff_L1 {d : ℕ} (f : Space d → ℝ) (hf : Integrable f) :
    Tendsto (fun ε : ℝ ↦ ∫ p : Space d, ‖innerCutoff ε f p - f p‖) (𝓝[>] 0) (𝓝 0) := by
  have h := tendsto_integral_filter_of_dominated_convergence
    (l := 𝓝[>] (0 : ℝ)) (μ := (volume : Measure (Space d)))
    (F := fun ε p ↦ ‖innerCutoff ε f p - f p‖) (f := fun _ ↦ (0 : ℝ)) (fun p ↦ 2 * ‖f p‖)
    (Filter.Eventually.of_forall (fun ε ↦
      ((hf.aestronglyMeasurable.indicator (measurableSet_innerCutoff d ε)).sub hf.aestronglyMeasurable).norm))
    (Filter.Eventually.of_forall (fun ε ↦ Filter.Eventually.of_forall (fun p ↦ ?_)))
    (hf.norm.const_mul 2) ?_
  · simpa only [integral_zero] using h
  · rw [Real.norm_of_nonneg (norm_nonneg _)]
    calc
      ‖innerCutoff ε f p - f p‖ ≤ ‖innerCutoff ε f p‖ + ‖f p‖ := norm_sub_le _ _
      _ ≤ ‖f p‖ + ‖f p‖ :=
        add_le_add (norm_indicator_le_norm_self (s := {q : Space d | ε < ‖q.1‖}) (f := f) (a := p)) le_rfl
      _ = 2 * ‖f p‖ := (two_mul _).symm
  · filter_upwards [ae_mem_regularLocus d] with p hp
    have hh := ((tendsto_innerCutoff_value f p hp).sub (tendsto_const_nhds (x := f p))).norm
    simpa only [sub_self, norm_zero] using hh

theorem tendsto_integral_innerCutoff {d : ℕ} (f : Space d → ℝ) (hf : Integrable f) :
    Tendsto (fun ε : ℝ ↦ ∫ p : Space d, innerCutoff ε f p) (𝓝[>] 0) (𝓝 (∫ p, f p)) := by
  apply tendsto_integral_filter_of_dominated_convergence (fun p ↦ ‖f p‖)
  · exact Filter.Eventually.of_forall (fun ε ↦
      hf.aestronglyMeasurable.indicator (measurableSet_innerCutoff d ε))
  · exact Filter.Eventually.of_forall (fun ε ↦ Filter.Eventually.of_forall
      (fun p ↦ norm_indicator_le_norm_self (f := f) (a := p)))
  · exact hf.norm
  · filter_upwards [ae_mem_regularLocus d] with p hp
    exact tendsto_innerCutoff_value f p hp

theorem integral_innerCutoff_density_eq_annulus_product {d : ℕ} (ω : ProductForm d)
    {R : ℝ} (hbound : SupportBound ω R) (ε : ℝ) :
    (∫ p : Space d, innerCutoff ε (density ω) p) =
      ∫ p in PolarAnnulus.annulus ε R ×ˢ passiveBox d R, density ω p := by
  rw [innerCutoff, integral_indicator (measurableSet_innerCutoff d ε)]
  apply CompactSupportBoxes.setIntegral_eq_of_support_inter_subset _ _ _
    (measurableSet_innerCutoff d ε)
  · exact fun p hp ↦ hp.1.1
  · rintro p ⟨hp, hε⟩
    have hs := CompactSupportBoxes.support_extDeriv_apply_subset ω (frame d) hp
    have hb := hbound p hs
    exact ⟨⟨hε, hb.1⟩, ⟨fun j ↦ (abs_lt.mp (hb.2 j)).1.le,
      fun j ↦ (abs_lt.mp (hb.2 j)).2.le⟩⟩

/-- Stokes across one deleted complex coordinate, with any number of passive
coordinates. The only boundary input is the limit of the actual cylinder integral. -/
theorem integral_extDeriv_eq_zero {d : ℕ} (ω : ProductForm d)
    (hω : ContDiffOn ℝ 1 ω (regularLocus d)) (hcompact : HasCompactSupport ω)
    (hL1 : Integrable (density ω))
    (hboundary : Tendsto (cylinderIntegral ω) (𝓝[>] 0) (𝓝 0)) :
    (∫ p : Space d, density ω p) = 0 := by
  obtain ⟨R, hR, hbound⟩ := exists_supportBound ω hcompact
  have hlim := tendsto_integral_innerCutoff (density ω) hL1
  have heq : (fun ε : ℝ ↦ ∫ p : Space d, innerCutoff ε (density ω) p) =ᶠ[𝓝[>] 0]
      (fun ε ↦ -cylinderIntegral ω ε) := by
    filter_upwards [Ioo_mem_nhdsGT hR] with ε hε
    rw [integral_innerCutoff_density_eq_annulus_product ω hbound ε,
      annulus_product_stokes ω hω hL1 hbound ε hε.1 hε.2]
  have hz : Tendsto (fun ε : ℝ ↦ -cylinderIntegral ω ε) (𝓝[>] 0) (𝓝 0) := by
    simpa only [neg_zero] using hboundary.neg
  exact tendsto_nhds_unique hlim (hz.congr' heq.symm)

theorem integral_extDeriv_frame_eq_zero {d : ℕ} (ω : ProductForm d)
    (hω : ContDiffOn ℝ 1 ω (regularLocus d)) (hcompact : HasCompactSupport ω)
    (hL1 : Integrable (fun p ↦ extDeriv ω p (frame d)))
    (hboundary : Tendsto (cylinderIntegral ω) (𝓝[>] 0) (𝓝 0)) :
    (∫ p : Space d, extDeriv ω p (frame d)) = 0 :=
  integral_extDeriv_eq_zero ω hω hcompact hL1 hboundary

/-- Adding zero passive coordinates is the genuine pullback along the first projection. -/
def liftZero (ω : PuncturedCoordinateStokes.OneForm) : ProductForm 0 :=
  fun p ↦ (ω p.1).compContinuousLinearMap (ContinuousLinearMap.fst ℝ ℂ (Coord 0))

theorem density_liftZero (ω : PuncturedCoordinateStokes.OneForm) (p : Space 0)
    (hω : DifferentiableAt ℝ ω p.1) : density (liftZero ω) p = PuncturedCoordinateStokes.density ω p.1 := by
  unfold density liftZero
  have h := extDeriv_pullback (r := ⊤) hω (ContinuousLinearMap.fst ℝ ℂ (Coord 0)).contDiff.contDiffAt (by simp)
  simp only [fderiv_fst] at h
  rw [h, ContinuousAlternatingMap.compContinuousLinearMap_apply]
  change extDeriv ω p.1 _ = extDeriv ω p.1 ![1, Complex.I]
  congr 1
  ext i
  fin_cases i <;> rfl

theorem cylinderDensity_liftZero (ω : PuncturedCoordinateStokes.OneForm)
    (r : ℝ) (x : Coord 1) :
    cylinderDensity (liftZero ω) r x = PuncturedCoordinateStokes.circleDensity ω r (x 0) := by
  rw [← radial_face_density, facePullback_standardBasis]
  unfold faceCoefficient polarPullback liftZero
  simp only [fderiv_polar, ContinuousAlternatingMap.compContinuousLinearMap_apply]
  change ω (LogCircle.shrinkingCircle r (x 0)) _ = _
  congr 1
  funext i
  rw [Subsingleton.elim i 0]
  change (polarDerivative _ (standardBasis 2 1)).1 = LogCircle.shrinkingCircleTangent r (x 0) 1
  rw [polarDerivative_one]
  simp [polar_fst, Fin.insertNth_zero', LogCircle.shrinkingCircleTangent_apply]

theorem cylinderIntegral_liftZero (ω : PuncturedCoordinateStokes.OneForm) (r : ℝ) :
    cylinderIntegral (liftZero ω) r = PuncturedCoordinateStokes.circleIntegral ω r := by
  unfold cylinderIntegral
  simp_rw [cylinderDensity_liftZero]
  have hs : cylinderStrip 0 = Icc (fun _ ↦ -Real.pi) (fun _ ↦ Real.pi) := by
    ext x
    simp [cylinderStrip, Pi.le_def, Fin.forall_fin_one]
  rw [hs, PuncturedCoordinateStokes.integral_finOne_Icc,
    PuncturedCoordinateStokes.circleIntegral_eq_centered,
    intervalIntegral.integral_of_le (show -Real.pi ≤ Real.pi by linarith [Real.pi_pos]),
    setIntegral_congr_set (Ioc_ae_eq_Icc (α := ℝ) (μ := volume))]

theorem integral_density_liftZero (ω : PuncturedCoordinateStokes.OneForm)
    (hω : ContDiffOn ℝ 1 ω ({0}ᶜ : Set ℂ)) :
    (∫ p : Space 0, density (liftZero ω) p) = ∫ z : ℂ, PuncturedCoordinateStokes.density ω z := by
  have heq : density (liftZero ω) =ᵐ[volume] (fun p : Space 0 ↦ PuncturedCoordinateStokes.density ω p.1) := by
    filter_upwards [ae_mem_regularLocus 0] with p hp
    apply density_liftZero
    exact (hω.contDiffAt (isClosed_singleton.isOpen_compl.mem_nhds hp)).differentiableAt (by decide)
  rw [integral_congr_ae heq, Measure.volume_eq_prod, integral_fun_fst]
  simp [Measure.real_def, volume_pi]

theorem contDiffOn_liftZero (ω : PuncturedCoordinateStokes.OneForm)
    (hω : ContDiffOn ℝ 1 ω ({0}ᶜ : Set ℂ)) : ContDiffOn ℝ 1 (liftZero ω) (regularLocus 0) := by
  intro p hp
  have hc := hω.contDiffAt (isClosed_singleton.isOpen_compl.mem_nhds hp)
  exact ((ContinuousAlternatingMap.compContinuousLinearMapCLM
    (ContinuousLinearMap.fst ℝ ℂ (Coord 0))).contDiff.contDiffAt.comp p
      (hc.comp p (ContinuousLinearMap.fst ℝ ℂ (Coord 0)).contDiff.contDiffAt)).contDiffWithinAt

theorem hasCompactSupport_liftZero (ω : PuncturedCoordinateStokes.OneForm)
    (hω : HasCompactSupport ω) : HasCompactSupport (liftZero ω) := by
  have hs : Function.support (liftZero ω) ⊆ tsupport ω ×ˢ ({0} : Set (Coord 0)) := by
    intro p hp
    constructor
    · apply subset_tsupport ω
      intro hz
      apply hp
      simp only [liftZero, hz]
      rfl
    · exact Subsingleton.elim p.2 0
  exact (hω.isCompact.prod isCompact_singleton).of_isClosed_subset (isClosed_tsupport _)
    (closure_minimal hs ((isClosed_tsupport ω).prod isClosed_singleton))

theorem integrable_density_liftZero (ω : PuncturedCoordinateStokes.OneForm)
    (hω : ContDiffOn ℝ 1 ω ({0}ᶜ : Set ℂ)) (hL1 : Integrable (PuncturedCoordinateStokes.density ω)) :
    Integrable (density (liftZero ω)) := by
  have h := hL1.comp_fst (volume : Measure (Coord 0))
  apply h.congr
  filter_upwards [ae_mem_regularLocus 0] with p hp
  exact (density_liftZero ω p
    ((hω.contDiffAt (isClosed_singleton.isOpen_compl.mem_nhds hp)).differentiableAt (by decide))).symm

/-- The zero-passive-dimensional specialization recovers the preceding one-coordinate
theorem with exactly its old hypotheses, now by the product-box proof. -/
theorem dimension_zero_recovers_coordinate_stokes (ω : PuncturedCoordinateStokes.OneForm)
    (hω : ContDiffOn ℝ 1 ω ({0}ᶜ : Set ℂ)) (hcompact : HasCompactSupport ω)
    (hL1 : Integrable (PuncturedCoordinateStokes.density ω))
    (hcircle : Tendsto (PuncturedCoordinateStokes.circleIntegral ω) (𝓝[>] 0) (𝓝 0)) :
    (∫ z : ℂ, extDeriv ω z ![1, Complex.I]) = 0 := by
  have hb : Tendsto (cylinderIntegral (liftZero ω)) (𝓝[>] 0) (𝓝 0) := by
    have heq : cylinderIntegral (liftZero ω) = PuncturedCoordinateStokes.circleIntegral ω :=
      funext (cylinderIntegral_liftZero ω)
    rwa [heq]
  have h := integral_extDeriv_eq_zero (liftZero ω) (contDiffOn_liftZero ω hω)
    (hasCompactSupport_liftZero ω hcompact) (integrable_density_liftZero ω hω hL1) hb
  rwa [integral_density_liftZero ω hω] at h

/-- Positive-radius cylinder densities are actual continuous functions. -/
theorem continuous_cylinderDensity {d : ℕ} (ω : ProductForm d)
    (hω : ContDiffOn ℝ 1 ω (regularLocus d)) {r : ℝ} (hr : 0 < r) :
    Continuous (cylinderDensity ω r) := by
  have heq : cylinderDensity ω r = fun x ↦
      polarPullback ω (faceEmbedding 0 r x) ((0 : Fin (d + 2)).removeNth (standardBasis (d + 2))) := by
    funext x
    rw [← radial_face_density, facePullback_standardBasis]
    rfl
  rw [heq]
  apply continuous_iff_continuousAt.mpr
  intro x
  have hc : ContDiffAt ℝ 1 ω (polar (faceEmbedding 0 r x)) :=
    hω.contDiffAt ((isOpen_regularLocus d).mem_nhds (polar_mem_regularLocus hr))
  exact (ContinuousAlternatingMap.apply ℝ _ ℝ _).continuous.continuousAt.comp
    ((differentiableAt_polarPullback ω _ hc).continuousAt.comp
      (hasFDerivAt_faceEmbedding 0 r x).continuousAt)

/-- Compact support proves finiteness of each positive-radius boundary integral;
no integrability of a supplied boundary expression is silently assumed. -/
theorem integrableOn_cylinderDensity {d : ℕ} (ω : ProductForm d)
    (hω : ContDiffOn ℝ 1 ω (regularLocus d)) (hcompact : HasCompactSupport ω)
    {r : ℝ} (hr : 0 < r) : IntegrableOn (cylinderDensity ω r) (cylinderStrip d) := by
  obtain ⟨R, hR, hbound⟩ := exists_supportBound ω hcompact
  let I := (polarBox d 0 R hR hR).face 0
  have hf : IntegrableOn (cylinderDensity ω r) (BoxIntegral.Box.Icc I) :=
    (continuous_cylinderDensity ω hω hr).continuousOn.integrableOn_compact I.isCompact_Icc
  apply hf.of_forall_sdiff_eq_zero
    ((measurableSet_le measurable_const (measurable_pi_apply 0)).inter
      (measurableSet_le (measurable_pi_apply 0) measurable_const))
  rintro x ⟨hx, hn⟩
  by_contra hz
  have hb (j : Fin d) : |x j.succ| < R :=
    lt_of_not_ge (fun hj ↦ hz (cylinderDensity_zero_of_passive_ge ω hbound r x j hj))
  apply hn
  constructor
  · intro i
    refine Fin.cases hx.1 (fun j ↦ ?_) i
    exact (abs_lt.mp (hb j)).1.le
  · intro i
    refine Fin.cases hx.2 (fun j ↦ ?_) i
    exact (abs_lt.mp (hb j)).2.le

end EnvelopingIsomorphism.Deformation.Kontsevich.PuncturedProductStokes
