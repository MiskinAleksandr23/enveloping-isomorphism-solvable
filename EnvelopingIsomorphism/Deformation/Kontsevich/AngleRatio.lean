import EnvelopingIsomorphism.Deformation.Kontsevich.Configuration
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# The complex ratio underlying the harmonic angle

The harmonic angle is obtained from the argument of `(q - p)/(q - conj p)`.
Here we establish its well-definedness on configurations, smoothness before
taking an argument, affine invariance, and its boundary-source restriction.
No global real-valued branch of the angle or graph integral is asserted.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich

open ComplexConjugate
open scoped UpperHalfPlane Topology

/-- Complex expression whose argument is the harmonic angle from `p` toward `q`. -/
def harmonicRatio (p q : ℂ) : ℂ := (q - p) / (q - conj p)

theorem harmonicDenominator_ne_zero {p q : ℂ} (hp : 0 < p.im) (hq : 0 ≤ q.im) :
    q - conj p ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  simp only [Complex.sub_im, Complex.conj_im, Complex.zero_im] at hi
  linarith

theorem harmonicRatio_ne_zero {p q : ℂ} (hp : 0 < p.im) (hq : 0 ≤ q.im)
    (hne : q ≠ p) : harmonicRatio p q ≠ 0 :=
  div_ne_zero (sub_ne_zero.mpr hne) (harmonicDenominator_ne_zero hp hq)

/-- The complex ratio is smooth wherever its denominator is nonzero. -/
theorem contDiffAt_harmonicRatio (p q : ℂ) (h : q - conj p ≠ 0) :
    ContDiffAt ℝ ⊤ (fun z : ℂ × ℂ => harmonicRatio z.1 z.2) (p, q) := by
  have hc : ContDiffAt ℝ ⊤ (fun z : ℂ × ℂ => conj z.1) (p, q) :=
    Complex.conjCLE.contDiff.contDiffAt.comp (p, q) contDiffAt_fst
  simpa only [harmonicRatio, div_eq_mul_inv, Pi.inv_apply] using
    (contDiffAt_snd.sub contDiffAt_fst).mul ((contDiffAt_snd.sub hc).inv h)

/-- Positive affine changes of coordinates do not change the ratio. -/
theorem harmonicRatio_affine (g : PositiveAffine) (p q : ℂ) :
    harmonicRatio ((g.scale : ℂ) * p + g.shift) ((g.scale : ℂ) * q + g.shift) =
      harmonicRatio p q := by
  have ha : (g.scale : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt g.scale_pos)
  simp only [harmonicRatio, map_add, map_mul, Complex.conj_ofReal]
  rw [show (g.scale : ℂ) * q + g.shift - ((g.scale : ℂ) * p + g.shift) =
    (g.scale : ℂ) * (q - p) by ring]
  rw [show (g.scale : ℂ) * q + g.shift - ((g.scale : ℂ) * conj p + g.shift) =
    (g.scale : ℂ) * (q - conj p) by ring]
  exact mul_div_mul_left _ _ ha

/-- Away from a collision, putting the source on the real boundary makes the ratio constant. -/
theorem harmonicRatio_boundary_source (p : ℝ) (q : ℂ) (hne : q ≠ (p : ℂ)) :
    harmonicRatio p q = 1 := by
  simp only [harmonicRatio, Complex.conj_ofReal]
  exact div_self (sub_ne_zero.mpr hne)

/-- The restriction to the boundary-source locus has zero derivative away from collisions. -/
theorem hasFDerivAt_harmonicRatio_boundary_source (p : ℝ) (q : ℂ)
    (hne : q ≠ (p : ℂ)) :
    HasFDerivAt (fun z : ℝ × ℂ => harmonicRatio z.1 z.2)
      (0 : (ℝ × ℂ) →L[ℝ] ℂ) (p, q) := by
  apply (hasFDerivAt_const (𝕜 := ℝ) (1 : ℂ) (p, q)).congr_of_eventuallyEq
  have hloc : ∀ᶠ z : ℝ × ℂ in 𝓝 (p, q), z.2 ≠ (z.1 : ℂ) :=
    (isOpen_ne_fun continuous_snd (Complex.continuous_ofReal.comp continuous_fst)).mem_nhds hne
  exact hloc.mono fun z hz => harmonicRatio_boundary_source z.1 z.2 hz

/-- For an interior source and a real target, the ratio lies on the unit circle. -/
theorem norm_harmonicRatio_boundary_target (p : ℍ) (q : ℝ) :
    ‖harmonicRatio p q‖ = 1 := by
  have hne : (q : ℂ) - (p : ℂ) ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.ofReal_im, UpperHalfPlane.coe_im,
      Complex.zero_im, zero_sub, neg_eq_zero] at hi
    exact p.im_ne_zero hi
  have hc : (q : ℂ) - conj (p : ℂ) = conj ((q : ℂ) - (p : ℂ)) := by simp
  rw [harmonicRatio, hc, norm_div, Complex.norm_conj]
  exact div_self (norm_ne_zero_iff.mpr hne)

namespace Configuration

variable {n m : ℕ}

theorem vertexPoint_im_nonneg (c : Configuration n m) (v : Fin n ⊕ Fin m) :
    0 ≤ (c.vertexPoint v).im := by
  cases v with
  | inl i => exact le_of_lt (c.interior i).im_pos
  | inr j => simp [vertexPoint]

/-- The denominator of the angle expression never vanishes at an interior source. -/
theorem vertex_harmonicDenominator_ne_zero (c : Configuration n m) (i : Fin n)
    (v : Fin n ⊕ Fin m) : c.vertexPoint v - conj (c.interior i : ℂ) ≠ 0 :=
  harmonicDenominator_ne_zero (c.interior i).im_pos (c.vertexPoint_im_nonneg v)

/-- Each non-loop graph edge gives a nonzero harmonic ratio. -/
theorem vertex_harmonicRatio_ne_zero (c : Configuration n m) (i : Fin n)
    (v : Fin n ⊕ Fin m) (h : v ≠ Sum.inl i) :
    harmonicRatio (c.interior i) (c.vertexPoint v) ≠ 0 := by
  apply harmonicRatio_ne_zero (c.interior i).im_pos (c.vertexPoint_im_nonneg v)
  intro hv
  exact h (c.vertexPoint_injective hv)

theorem act_vertexPoint (g : PositiveAffine) (c : Configuration n m)
    (v : Fin n ⊕ Fin m) :
    (act g c).vertexPoint v = (g.scale : ℂ) * c.vertexPoint v + g.shift := by
  cases v with
  | inl i => exact PositiveAffine.coe_onUpper g _
  | inr j => simp [vertexPoint, PositiveAffine.onReal]

/-- The ratio assigned to a graph edge is independent of the affine representative. -/
theorem vertex_harmonicRatio_act (g : PositiveAffine) (c : Configuration n m)
    (i : Fin n) (v : Fin n ⊕ Fin m) :
    harmonicRatio ((act g c).interior i) ((act g c).vertexPoint v) =
      harmonicRatio (c.interior i) (c.vertexPoint v) := by
  rw [act_interior, PositiveAffine.coe_onUpper, act_vertexPoint]
  exact harmonicRatio_affine g _ _

/-- Actual complex edge data on the affine orbit quotient. -/
def quotientHarmonicRatio (i : Fin n) (v : Fin n ⊕ Fin m) : AffineQuotient n m → ℂ :=
  Quotient.lift (fun c => harmonicRatio (c.interior i) (c.vertexPoint v)) (by
    rintro c d ⟨g, rfl⟩
    exact (vertex_harmonicRatio_act g c i v).symm)

end Configuration

end EnvelopingIsomorphism.Deformation.Kontsevich
