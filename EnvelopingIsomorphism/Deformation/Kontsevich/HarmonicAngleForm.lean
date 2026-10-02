import EnvelopingIsomorphism.Deformation.Kontsevich.AngleRatio
import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# The global angular form and the harmonic angular form

The angular form on the punctured complex plane is `Im(dz / z)`. It is defined
without choosing a real-valued argument. Its pullback by `harmonicRatio` is the
harmonic angular form used on configuration spaces.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich

open ComplexConjugate
open scoped UpperHalfPlane

/-- A complex coefficient acts as the real linear functional `v ↦ Im(a * v)`. -/
def angularLinearCoefficient : ℂ →L[ℝ] (ℂ →L[ℝ] ℝ) :=
  ((ContinuousLinearMap.compL ℝ ℂ ℂ ℝ) Complex.imCLM).comp
    (ContinuousLinearMap.mul ℝ ℂ)

/-- Convert a complex coefficient into the real one-form `v ↦ Im(a * v)`. -/
def angularCoefficient : ℂ →L[ℝ] ℂ [⋀^Fin 1]→L[ℝ] ℝ :=
  (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := ℂ) (F := ℝ)
      (0 : Fin 1)).toContinuousLinearEquiv.toContinuousLinearMap.comp
    angularLinearCoefficient

@[simp] theorem angularCoefficient_apply (a : ℂ) (v : Fin 1 → ℂ) :
    angularCoefficient a v = (a * v 0).im := rfl

/-- The global angular one-form; its smooth domain is the punctured complex plane. -/
def angularForm (z : ℂ) : ℂ [⋀^Fin 1]→L[ℝ] ℝ := angularCoefficient z⁻¹

@[simp] theorem angularForm_apply (z : ℂ) (v : Fin 1 → ℂ) :
    angularForm z v = (v 0 / z).im := by
  simp [angularForm, div_eq_mul_inv, mul_comm]

theorem contDiffAt_angularForm {z : ℂ} (hz : z ≠ 0) : ContDiffAt ℝ ⊤ angularForm z :=
  angularCoefficient.contDiff.contDiffAt.comp z (contDiffAt_id.inv hz)

theorem hasFDerivAt_angularForm {z : ℂ} (hz : z ≠ 0) :
    HasFDerivAt angularForm
      (angularCoefficient.comp (-((ContinuousLinearMap.mulLeftRight ℝ ℂ) z⁻¹) z⁻¹)) z :=
  angularCoefficient.hasFDerivAt.comp z (hasFDerivAt_inv' hz)

/-- The angular form is closed on the punctured complex plane. -/
theorem extDeriv_angularForm {z : ℂ} (hz : z ≠ 0) : extDeriv angularForm z = 0 := by
  rw [extDeriv, (hasFDerivAt_angularForm hz).fderiv]
  ext v
  simp [ContinuousAlternatingMap.alternatizeUncurryFin_apply, Fin.sum_univ_two,
    angularCoefficient, angularLinearCoefficient, ContinuousLinearMap.mulLeftRight, Fin.removeNth,
    Complex.mul_im, Complex.mul_re]
  ring

/-- Pullback of the global angular form along the harmonic ratio. -/
def harmonicAngleForm (z : ℂ × ℂ) : (ℂ × ℂ) [⋀^Fin 1]→L[ℝ] ℝ :=
  (angularForm (harmonicRatio z.1 z.2)).compContinuousLinearMap
    (fderiv ℝ (fun z : ℂ × ℂ => harmonicRatio z.1 z.2) z)

theorem harmonicAngleForm_eq (z : ℂ × ℂ) :
    harmonicAngleForm z = ContinuousAlternatingMap.ofSubsingletonLIE (0 : Fin 1)
      ((angularLinearCoefficient (harmonicRatio z.1 z.2)⁻¹).comp
        (fderiv ℝ (fun z : ℂ × ℂ => harmonicRatio z.1 z.2) z)) := by
  ext v
  rfl

/-- The pulled-back angular form is smooth on the nonzero-ratio domain. -/
theorem contDiffAt_harmonicAngleForm (p q : ℂ) (hd : q - conj p ≠ 0)
    (hr : harmonicRatio p q ≠ 0) : ContDiffAt ℝ ⊤ harmonicAngleForm (p, q) := by
  have hf := contDiffAt_harmonicRatio p q hd
  have heq := funext harmonicAngleForm_eq
  rw [heq]
  exact (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := ℂ × ℂ) (F := ℝ)
    (0 : Fin 1)).contDiff.contDiffAt.comp (p, q)
      ((angularLinearCoefficient.contDiff.contDiffAt.comp (p, q) (hf.inv hr)).clm_comp
        (hf.fderiv_right (by simp)))

/-- Closedness follows from naturality of the exterior derivative. -/
theorem extDeriv_harmonicAngleForm (p q : ℂ) (hd : q - conj p ≠ 0)
    (hr : harmonicRatio p q ≠ 0) : extDeriv harmonicAngleForm (p, q) = 0 := by
  have hf := contDiffAt_harmonicRatio p q hd
  have hω := (contDiffAt_angularForm hr).differentiableAt (by simp)
  change extDeriv (fun z : ℂ × ℂ =>
    (angularForm (harmonicRatio z.1 z.2)).compContinuousLinearMap
      (fderiv ℝ (fun z : ℂ × ℂ => harmonicRatio z.1 z.2) z)) (p, q) = 0
  rw [extDeriv_pullback (f := fun z : ℂ × ℂ => harmonicRatio z.1 z.2)
    (x := (p, q)) hω hf (by simp), extDeriv_angularForm hr]
  ext v
  rfl

@[simp] theorem harmonicAngleForm_apply (z : ℂ × ℂ) (v : Fin 1 → ℂ × ℂ) :
    harmonicAngleForm z v =
      ((fderiv ℝ (fun z : ℂ × ℂ => harmonicRatio z.1 z.2) z (v 0)) /
        harmonicRatio z.1 z.2).im := by
  rw [harmonicAngleForm, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    angularForm_apply]
  rfl

/-- Pullbacks of the harmonic form can be calculated by the chain rule for the ratio. -/
theorem harmonicAngleForm_pullback {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℂ × ℂ) (x : E) (hf : DifferentiableAt ℝ f x)
    (hd : (f x).2 - conj (f x).1 ≠ 0) :
    (harmonicAngleForm (f x)).compContinuousLinearMap (fderiv ℝ f x) =
      (angularForm (harmonicRatio (f x).1 (f x).2)).compContinuousLinearMap
        (fderiv ℝ ((fun z : ℂ × ℂ => harmonicRatio z.1 z.2) ∘ f) x) := by
  rw [fderiv_comp x
    ((contDiffAt_harmonicRatio (f x).1 (f x).2 hd).differentiableAt (by simp)) hf]
  ext v
  rfl

/-- The simultaneous affine coordinate map on a pair of complex points. -/
def affinePair (g : PositiveAffine) (z : ℂ × ℂ) : ℂ × ℂ :=
  g.scale • z + ((g.shift : ℂ), (g.shift : ℂ))

def affinePairTangent (g : PositiveAffine) : (ℂ × ℂ) →L[ℝ] ℂ × ℂ :=
  g.scale • ContinuousLinearMap.id ℝ (ℂ × ℂ)

theorem hasFDerivAt_affinePair (g : PositiveAffine) (z : ℂ × ℂ) :
    HasFDerivAt (affinePair g) (affinePairTangent g) z :=
  ((hasFDerivAt_id z).const_smul g.scale).add_const _

theorem harmonicRatio_affinePair (g : PositiveAffine) (z : ℂ × ℂ) :
    harmonicRatio (affinePair g z).1 (affinePair g z).2 = harmonicRatio z.1 z.2 := by
  simpa [affinePair, Complex.real_smul] using harmonicRatio_affine g z.1 z.2

/-- Affine invariance holds as an equality of pulled-back one-forms. -/
theorem harmonicAngleForm_affine (g : PositiveAffine) (z : ℂ × ℂ)
    (hd : z.2 - conj z.1 ≠ 0) :
    (harmonicAngleForm (affinePair g z)).compContinuousLinearMap (affinePairTangent g) =
      harmonicAngleForm z := by
  have ha : (g.scale : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt g.scale_pos)
  have hd' : (affinePair g z).2 - conj (affinePair g z).1 ≠ 0 := by
    have heq : (affinePair g z).2 - conj (affinePair g z).1 =
        (g.scale : ℂ) * (z.2 - conj z.1) := by
      simp only [affinePair, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
        Complex.real_smul, map_add, map_mul, Complex.conj_ofReal]
      ring
    rw [heq]
    exact mul_ne_zero ha hd
  rw [← (hasFDerivAt_affinePair g z).fderiv,
    harmonicAngleForm_pullback _ _ (hasFDerivAt_affinePair g z).differentiableAt hd']
  have heq : (fun p : ℂ × ℂ => harmonicRatio p.1 p.2) ∘ affinePair g =
      fun p : ℂ × ℂ => harmonicRatio p.1 p.2 := funext (harmonicRatio_affinePair g)
  rw [heq, harmonicRatio_affinePair]
  rfl

/-- Inclusion of the boundary-source locus in the space of pairs. -/
def boundarySourceEmbedding : (ℝ × ℂ) →L[ℝ] ℂ × ℂ :=
  Complex.ofRealCLM.prodMap (ContinuousLinearMap.id ℝ ℂ)

/-- The harmonic angular form restricts to zero when its source lies on the real boundary. -/
theorem harmonicAngleForm_boundary_source (p : ℝ) (q : ℂ) (hne : q ≠ (p : ℂ)) :
    (harmonicAngleForm ((p : ℂ), q)).compContinuousLinearMap boundarySourceEmbedding = 0 := by
  have hd : q - conj (p : ℂ) ≠ 0 := by simpa using sub_ne_zero.mpr hne
  have hp := harmonicAngleForm_pullback boundarySourceEmbedding (p, q)
    boundarySourceEmbedding.differentiableAt hd
  rw [boundarySourceEmbedding.fderiv] at hp
  change (harmonicAngleForm ((p : ℂ), q)).compContinuousLinearMap boundarySourceEmbedding =
    (angularForm (harmonicRatio p q)).compContinuousLinearMap
      (fderiv ℝ (fun z : ℝ × ℂ => harmonicRatio z.1 z.2) (p, q)) at hp
  rw [hp]
  change (angularForm (harmonicRatio p q)).compContinuousLinearMap
    (fderiv ℝ (fun z : ℝ × ℂ => harmonicRatio z.1 z.2) (p, q)) = 0
  rw [(hasFDerivAt_harmonicRatio_boundary_source p q hne).fderiv]
  ext v
  simp

/-- One interior point is fixed at `I`, while its boundary target has coordinate `x`. -/
def normalizedBoundaryTarget (x : ℝ) : ℂ × ℂ := (Complex.I, (x : ℂ))

def normalizedBoundaryTangent : ℝ →L[ℝ] ℂ × ℂ :=
  (0 : ℝ →L[ℝ] ℂ).prod Complex.ofRealCLM

theorem hasFDerivAt_normalizedBoundaryTarget (x : ℝ) :
    HasFDerivAt normalizedBoundaryTarget normalizedBoundaryTangent x :=
  (hasFDerivAt_const Complex.I x).prodMk Complex.ofRealCLM.hasFDerivAt

theorem ofReal_add_I_ne_zero (x : ℝ) : (x : ℂ) + Complex.I ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  norm_num at hi

theorem ofReal_sub_I_ne_zero (x : ℝ) : (x : ℂ) - Complex.I ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  norm_num at hi

theorem hasDerivAt_normalizedBoundaryRatio (x : ℝ) :
    HasDerivAt (fun y : ℝ => harmonicRatio Complex.I y)
      (2 * Complex.I / ((x : ℂ) + Complex.I) ^ 2) x := by
  have hf : HasDerivAt (fun y : ℝ => (y : ℂ) - Complex.I) 1 x := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).sub_const Complex.I
  have hg : HasDerivAt (fun y : ℝ => (y : ℂ) + Complex.I) 1 x := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).add_const Complex.I
  convert! hf.fun_div hg (ofReal_add_I_ne_zero x) using 1
  · funext y
    simp [harmonicRatio]
  · congr 1
    ring

theorem normalizedBoundary_logDerivative (x v : ℝ) :
    (((v : ℂ) * (2 * Complex.I / ((x : ℂ) + Complex.I) ^ 2)) /
      harmonicRatio Complex.I x).im = (2 / (1 + x ^ 2)) * v := by
  have hplus := ofReal_add_I_ne_zero x
  have hminus := ofReal_sub_I_ne_zero x
  have hreal : (1 + x ^ 2 : ℝ) ≠ 0 := ne_of_gt (by positivity)
  have hcomplex : (1 + (x : ℂ) ^ 2) ≠ 0 := by exact_mod_cast hreal
  have heq : ((v : ℂ) * (2 * Complex.I / ((x : ℂ) + Complex.I) ^ 2)) /
      harmonicRatio Complex.I x = ((2 / (1 + x ^ 2) * v : ℝ) : ℂ) * Complex.I := by
    simp only [harmonicRatio, Complex.conj_I, sub_neg_eq_add, Complex.ofReal_mul,
      Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_pow,
      Complex.ofReal_ofNat, Complex.ofReal_one]
    field_simp [hplus, hminus, hcomplex]
    ring_nf
    simp [Complex.I_sq]
    ring
  rw [heq]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.ofReal_im,
    Complex.I_re, mul_one, mul_zero, add_zero]

/-- The actual pulled-back edge form has the Cauchy-density coefficient `2/(1+x²)`. -/
theorem harmonicAngleForm_normalized_boundary (x : ℝ) (v : Fin 1 → ℝ) :
    ((harmonicAngleForm (normalizedBoundaryTarget x)).compContinuousLinearMap
      normalizedBoundaryTangent) v = (2 / (1 + x ^ 2)) * v 0 := by
  have hd : (normalizedBoundaryTarget x).2 - conj (normalizedBoundaryTarget x).1 ≠ 0 := by
    simpa [normalizedBoundaryTarget] using ofReal_add_I_ne_zero x
  rw [← (hasFDerivAt_normalizedBoundaryTarget x).fderiv,
    harmonicAngleForm_pullback _ _ (hasFDerivAt_normalizedBoundaryTarget x).differentiableAt hd]
  change ((angularForm (harmonicRatio Complex.I x)).compContinuousLinearMap
    (fderiv ℝ (fun y : ℝ => harmonicRatio Complex.I y) x)) v = _
  rw [(hasDerivAt_normalizedBoundaryRatio x).hasFDerivAt.fderiv,
    ContinuousAlternatingMap.compContinuousLinearMap_apply, angularForm_apply]
  simpa [ContinuousLinearMap.smulRight_apply, Complex.real_smul] using
    normalizedBoundary_logDerivative x (v 0)

namespace Configuration

variable {n m : ℕ}

/-- Every non-loop configuration edge lies in the smooth domain of the actual angular form. -/
theorem contDiffAt_vertex_harmonicAngleForm (c : Configuration n m) (i : Fin n)
    (v : Fin n ⊕ Fin m) (hv : v ≠ Sum.inl i) :
    ContDiffAt ℝ ⊤ harmonicAngleForm ((c.interior i : ℂ), c.vertexPoint v) :=
  contDiffAt_harmonicAngleForm _ _ (c.vertex_harmonicDenominator_ne_zero i v)
    (c.vertex_harmonicRatio_ne_zero i v hv)

/-- The angular form is closed at every non-loop configuration edge. -/
theorem extDeriv_vertex_harmonicAngleForm (c : Configuration n m) (i : Fin n)
    (v : Fin n ⊕ Fin m) (hv : v ≠ Sum.inl i) :
    extDeriv harmonicAngleForm ((c.interior i : ℂ), c.vertexPoint v) = 0 :=
  extDeriv_harmonicAngleForm _ _ (c.vertex_harmonicDenominator_ne_zero i v)
    (c.vertex_harmonicRatio_ne_zero i v hv)

end Configuration

end EnvelopingIsomorphism.Deformation.Kontsevich
