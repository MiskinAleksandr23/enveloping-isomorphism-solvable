import EnvelopingIsomorphism.Deformation.Kontsevich.BoxStokes
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
Localization of genuinely compactly supported functions and differential forms
to finite coordinate boxes. The support bounds are proved from compactness,
and the derivative support bounds use the actual Fréchet derivative. No Stokes
formula, orthant decomposition, or global boundary identity is assumed.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.CompactSupportBoxes

open Set Function MeasureTheory

section CoordinateBounds

variable {d : ℕ} {A : Type*} [Zero A]

/-- A genuinely compact support lies strictly inside some positive coordinate box. -/
theorem exists_pos_tsupport_bound (f : (Fin d → ℝ) → A) (hf : HasCompactSupport f) :
    ∃ R : ℝ, 0 < R ∧ ∀ x ∈ tsupport f, ∀ i : Fin d, |x i| < R := by
  obtain ⟨R, hR, hbound⟩ := hf.isCompact.isBounded.exists_pos_norm_lt
  refine ⟨R, hR, fun x hx i => ?_⟩
  have hi : |x i| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x i
  exact hi.trans_lt (hbound x hx)

theorem notMem_tsupport_of_abs_ge (f : (Fin d → ℝ) → A) {R : ℝ}
    (hbound : ∀ x ∈ tsupport f, ∀ i : Fin d, |x i| < R)
    (x : Fin d → ℝ) (i : Fin d) (hxi : R ≤ |x i|) : x ∉ tsupport f :=
  fun hx => (not_lt_of_ge hxi) (hbound x hx i)

/-- Every function with the proved strict support bound vanishes on all far faces. -/
theorem zero_of_abs_ge (f : (Fin d → ℝ) → A) {R : ℝ}
    (hbound : ∀ x ∈ tsupport f, ∀ i : Fin d, |x i| < R)
    (x : Fin d → ℝ) (i : Fin d) (hxi : R ≤ |x i|) : f x = 0 :=
  image_eq_zero_of_notMem_tsupport (notMem_tsupport_of_abs_ge f hbound x i hxi)

theorem zero_faceEmbedding_of_abs_ge {n : ℕ} (f : BoxStokes.Coord (n + 1) → A) {R c : ℝ}
    (hbound : ∀ x ∈ tsupport f, ∀ i : Fin (n + 1), |x i| < R)
    (i : Fin (n + 1)) (hc : R ≤ |c|) (x : BoxStokes.Coord n) :
    f (BoxStokes.faceEmbedding i c x) = 0 := by
  apply zero_of_abs_ge f hbound _ i
  simpa only [BoxStokes.faceEmbedding, Fin.insertNth_apply_same] using hc

end CoordinateBounds

section DerivativeSupport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {n : ℕ}

/-- Exterior differentiation is identically zero outside the original topological support. -/
theorem extDeriv_zero_of_notMem_tsupport
    (ω : E → E [⋀^Fin n]→L[ℝ] ℝ) {x : E} (hx : x ∉ tsupport ω) : extDeriv ω x = 0 := by
  rw [extDeriv, fderiv_of_notMem_tsupport ℝ hx]
  exact (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E ℝ).map_zero

/-- The actual exterior derivative has no support outside the original support closure. -/
theorem support_extDeriv_subset (ω : E → E [⋀^Fin n]→L[ℝ] ℝ) :
    Function.support (extDeriv ω) ⊆ tsupport ω := by
  intro x hx
  by_contra hnot
  exact hx (extDeriv_zero_of_notMem_tsupport ω hnot)

/-- The stronger topological-support inclusion. -/
theorem tsupport_extDeriv_subset (ω : E → E [⋀^Fin n]→L[ℝ] ℝ) :
    tsupport (extDeriv ω) ⊆ tsupport ω :=
  closure_minimal (support_extDeriv_subset ω) (isClosed_tsupport ω)

theorem hasCompactSupport_extDeriv (ω : E → E [⋀^Fin n]→L[ℝ] ℝ)
    (hω : HasCompactSupport ω) : HasCompactSupport (extDeriv ω) :=
  hω.mono' (support_extDeriv_subset ω)

/-- Evaluation of a differential form on any fixed tuple cannot enlarge support. -/
theorem support_form_apply_subset (ω : E → E [⋀^Fin n]→L[ℝ] ℝ) (v : Fin n → E) :
    Function.support (fun x => ω x v) ⊆ tsupport ω := by
  intro x hx
  by_contra hnot
  have hzero : ω x = 0 := image_eq_zero_of_notMem_tsupport hnot
  apply hx
  change ω x v = 0
  rw [hzero]
  rfl

theorem support_extDeriv_apply_subset (ω : E → E [⋀^Fin n]→L[ℝ] ℝ)
    (v : Fin (n + 1) → E) :
    Function.support (fun x => extDeriv ω x v) ⊆ tsupport ω :=
  (support_form_apply_subset (extDeriv ω) v).trans (tsupport_extDeriv_subset ω)

end DerivativeSupport

/-- The body coefficient used by box Stokes is supported in the original compact support. -/
theorem support_extDeriv_density_subset {n : ℕ} (ω : BoxStokes.Form n) :
    Function.support (fun x => extDeriv ω x (BoxStokes.standardBasis (n + 1))) ⊆ tsupport ω :=
  support_extDeriv_apply_subset ω _

/-- The whole pulled-back form vanishes on a far coordinate face, not only its density. -/
theorem facePullback_zero_of_abs_ge {n : ℕ} (ω : BoxStokes.Form n) {R c : ℝ}
    (hbound : ∀ x ∈ tsupport ω, ∀ i : Fin (n + 1), |x i| < R)
    (i : Fin (n + 1)) (hc : R ≤ |c|) (x : BoxStokes.Coord n) :
    BoxStokes.facePullback ω i c x = 0 := by
  rw [BoxStokes.facePullback, zero_faceEmbedding_of_abs_ge ω hbound i hc x]
  ext v
  rfl

/-- The same strict box contains the exterior derivative and all its coefficients. -/
theorem extDeriv_zero_of_abs_ge {n : ℕ} (ω : BoxStokes.Form n) {R : ℝ}
    (hbound : ∀ x ∈ tsupport ω, ∀ i : Fin (n + 1), |x i| < R)
    (x : BoxStokes.Coord (n + 1)) (i : Fin (n + 1)) (hxi : R ≤ |x i|) :
    extDeriv ω x = 0 :=
  extDeriv_zero_of_notMem_tsupport ω (notMem_tsupport_of_abs_ge ω hbound x i hxi)

section IntegralLocalization

variable {X : Type*} [MeasurableSpace X]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {μ : Measure X}

/-- Integration over the whole space localizes to any set containing the actual support. -/
theorem integral_eq_setIntegral_of_support_subset (f : X → F) (s : Set X)
    (hs : Function.support f ⊆ s) :
    (∫ x, f x ∂μ) = ∫ x in s, f x ∂μ := by
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  exact Function.notMem_support.mp (fun hfx => hx (hs hfx))

/-- A measurable region, such as a closed orthant, localizes to any contained
finite box that contains the intersection with the actual support. -/
theorem setIntegral_eq_of_support_inter_subset (f : X → F) (s t : Set X)
    (hs : MeasurableSet s) (hts : t ⊆ s) (hsupport : Function.support f ∩ s ⊆ t) :
    (∫ x in s, f x ∂μ) = ∫ x in t, f x ∂μ := by
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hs hts
  intro x hx
  exact Function.notMem_support.mp (fun hfx => hx.2 (hsupport ⟨hfx, hx.1⟩))

end IntegralLocalization

/-- Full-space localization of the actual exterior-derivative density. -/
theorem integral_extDeriv_density_eq_setIntegral {n : ℕ} (ω : BoxStokes.Form n)
    (s : Set (BoxStokes.Coord (n + 1))) (hs : tsupport ω ⊆ s) :
    (∫ x, extDeriv ω x (BoxStokes.standardBasis (n + 1))) =
      ∫ x in s, extDeriv ω x (BoxStokes.standardBasis (n + 1)) :=
  integral_eq_setIntegral_of_support_subset _ s ((support_extDeriv_density_subset ω).trans hs)

/-- Orthant/box localization only needs the original support bound, because
the actual exterior derivative has already been proved to have smaller support. -/
theorem setIntegral_extDeriv_density_eq_of_subset {n : ℕ} (ω : BoxStokes.Form n)
    (s t : Set (BoxStokes.Coord (n + 1))) (hs : MeasurableSet s) (hts : t ⊆ s)
    (hsupport : tsupport ω ∩ s ⊆ t) :
    (∫ x in s, extDeriv ω x (BoxStokes.standardBasis (n + 1))) =
      ∫ x in t, extDeriv ω x (BoxStokes.standardBasis (n + 1)) := by
  apply setIntegral_eq_of_support_inter_subset _ s t hs hts
  intro x hx
  exact hsupport ⟨support_extDeriv_density_subset ω hx.1, hx.2⟩

/-- A continuously differentiable compactly supported form has a genuinely
Lebesgue-integrable exterior-derivative density on the whole coordinate space. -/
theorem integrable_extDeriv_density {n : ℕ} (ω : BoxStokes.Form n)
    (hω : ContDiff ℝ 1 ω) (hcompact : HasCompactSupport ω) :
    Integrable (fun x => extDeriv ω x (BoxStokes.standardBasis (n + 1))) := by
  have hder : Continuous (fderiv ℝ ω) :=
    continuous_iff_continuousAt.mpr (fun x => hω.contDiffAt.continuousAt_fderiv (by decide))
  have hcoeff : Continuous (fun x => extDeriv ω x (BoxStokes.standardBasis (n + 1))) := by
    exact (ContinuousAlternatingMap.apply ℝ _ ℝ (BoxStokes.standardBasis (n + 1))).continuous.comp
      ((ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ _ ℝ).continuous.comp hder)
  exact hcoeff.integrable_of_hasCompactSupport (hcompact.mono' (support_extDeriv_density_subset ω))

end EnvelopingIsomorphism.Deformation.Kontsevich.CompactSupportBoxes
