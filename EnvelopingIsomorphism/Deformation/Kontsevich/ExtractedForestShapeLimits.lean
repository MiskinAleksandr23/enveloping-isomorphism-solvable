import EnvelopingIsomorphism.Deformation.Kontsevich.ReflectedForestExtraction

/-! Coordinate signs and equalities in actual extracted shape differences.
The hypotheses concern original point differences. They are transferred by
the genuine positive-real normalization and the proved common-subsequence limit. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.ExtractedForestShapeLimits

open Filter Topology ComplexConjugate Configuration
open SubsetNormalizedLimits (LargeSubset)
open ReflectedSubsetNormalization

variable {I : Type*} [Fintype I]
variable {σ : I → I} {hσ : Function.Involutive σ} {p : ℕ → I → ℂ}

theorem tendsto_shape_sub (E : ReflectedForestExtraction.Extraction σ hσ p)
    (A : LargeSubset I) (j k : A.val) :
    Tendsto (fun r => normalizedOn σ hσ A (p (E.subsequence r)) j -
      normalizedOn σ hσ A (p (E.subsequence r)) k) atTop (𝓝 (E.shapes A j - E.shapes A k)) := by
  have hc : Continuous (fun x : A.val → ℂ => x j - x k) := (continuous_apply j).sub (continuous_apply k)
  simpa only [Function.comp_def] using (hc.tendsto (E.shapes A)).comp (E.limits A)

theorem shape_sub_re_nonneg (E : ReflectedForestExtraction.Extraction σ hσ p)
    (A : LargeSubset I) (j k : A.val) (hp : ∀ r, 0 ≤ (p r j - p r k).re) :
    0 ≤ (E.shapes A j - E.shapes A k).re := by
  have h := Complex.continuous_re.continuousAt.tendsto.comp (tendsto_shape_sub E A j k)
  apply ge_of_tendsto h
  apply Eventually.of_forall
  intro r
  change 0 ≤ (normalizedOn σ hσ A (p (E.subsequence r)) j - normalizedOn σ hσ A (p (E.subsequence r)) k).re
  rw [normalizedOn_sub, Complex.smul_re, smul_eq_mul]
  exact mul_nonneg (inv_nonneg.mpr (radiusOn_nonneg σ hσ A (p (E.subsequence r)))) (hp (E.subsequence r))

theorem shape_sub_im_nonneg (E : ReflectedForestExtraction.Extraction σ hσ p)
    (A : LargeSubset I) (j k : A.val) (hp : ∀ r, 0 ≤ (p r j - p r k).im) :
    0 ≤ (E.shapes A j - E.shapes A k).im := by
  have h := Complex.continuous_im.continuousAt.tendsto.comp (tendsto_shape_sub E A j k)
  apply ge_of_tendsto h
  apply Eventually.of_forall
  intro r
  change 0 ≤ (normalizedOn σ hσ A (p (E.subsequence r)) j - normalizedOn σ hσ A (p (E.subsequence r)) k).im
  rw [normalizedOn_sub, Complex.smul_im, smul_eq_mul]
  exact mul_nonneg (inv_nonneg.mpr (radiusOn_nonneg σ hσ A (p (E.subsequence r)))) (hp (E.subsequence r))

theorem shape_sub_re_eq_zero (E : ReflectedForestExtraction.Extraction σ hσ p)
    (A : LargeSubset I) (j k : A.val) (hp : ∀ r, (p r j - p r k).re = 0) :
    (E.shapes A j - E.shapes A k).re = 0 := by
  have h := Complex.continuous_re.continuousAt.tendsto.comp (tendsto_shape_sub E A j k)
  apply tendsto_nhds_unique h
  have heq : (fun r => (normalizedOn σ hσ A (p (E.subsequence r)) j -
      normalizedOn σ hσ A (p (E.subsequence r)) k).re) = fun _ : ℕ => (0 : ℝ) := by
    funext r
    rw [normalizedOn_sub, Complex.smul_re, hp, smul_zero]
  simp only [Function.comp_def]
  rw [heq]
  exact tendsto_const_nhds

theorem shape_sub_im_eq_zero (E : ReflectedForestExtraction.Extraction σ hσ p)
    (A : LargeSubset I) (j k : A.val) (hp : ∀ r, (p r j - p r k).im = 0) :
    (E.shapes A j - E.shapes A k).im = 0 := by
  have h := Complex.continuous_im.continuousAt.tendsto.comp (tendsto_shape_sub E A j k)
  apply tendsto_nhds_unique h
  have heq : (fun r => (normalizedOn σ hσ A (p (E.subsequence r)) j -
      normalizedOn σ hσ A (p (E.subsequence r)) k).im) = fun _ : ℕ => (0 : ℝ) := by
    funext r
    rw [normalizedOn_sub, Complex.smul_im, hp, smul_zero]
  simp only [Function.comp_def]
  rw [heq]
  exact tendsto_const_nhds

section Doubled

variable {n m : ℕ}

theorem doubledSequence_upper_sub_conjugate_re (i : Fin n) (x : Compactification i m)
    (r : ℕ) (j : Fin n) :
    (CompactificationClusterLimits.doubledSequence i x r (Sum.inl (Sum.inl j)) -
      CompactificationClusterLimits.doubledSequence i x r (Sum.inr j)).re = 0 := by
  simp [CompactificationClusterLimits.doubledSequence, doubledPoint, vertexPoint]

theorem doubledSequence_upper_sub_conjugate_im_pos (i : Fin n) (x : Compactification i m)
    (r : ℕ) (j : Fin n) :
    0 < (CompactificationClusterLimits.doubledSequence i x r (Sum.inl (Sum.inl j)) -
      CompactificationClusterLimits.doubledSequence i x r (Sum.inr j)).im := by
  have h := ((normalizedSequence i x r).val.interior j).im_pos
  simpa only [CompactificationClusterLimits.doubledSequence, doubledPoint, vertexPoint,
    Sum.elim_inl, Complex.sub_im, Complex.conj_im, sub_neg_eq_add, UpperHalfPlane.coe_im] using add_pos h h

theorem doubledSequence_boundary_sub_im (i : Fin n) (x : Compactification i m)
    (r : ℕ) (j k : Fin m) :
    (CompactificationClusterLimits.doubledSequence i x r (Sum.inl (Sum.inr k)) -
      CompactificationClusterLimits.doubledSequence i x r (Sum.inl (Sum.inr j))).im = 0 := by
  simp [CompactificationClusterLimits.doubledSequence, doubledPoint, vertexPoint]

theorem doubledSequence_boundary_sub_re_pos (i : Fin n) (x : Compactification i m)
    (r : ℕ) (j k : Fin m) (hjk : j < k) :
    0 < (CompactificationClusterLimits.doubledSequence i x r (Sum.inl (Sum.inr k)) -
      CompactificationClusterLimits.doubledSequence i x r (Sum.inl (Sum.inr j))).re := by
  simpa only [CompactificationClusterLimits.doubledSequence, doubledPoint, vertexPoint,
    Sum.elim_inr, Complex.sub_re, Complex.ofReal_re] using
    sub_pos.mpr ((normalizedSequence i x r).val.boundary_strictMono hjk)

end Doubled

end EnvelopingIsomorphism.Deformation.Kontsevich.ExtractedForestShapeLimits
