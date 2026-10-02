import EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryClusterChart

/-!
Reconstruct finite real-cluster parameters from actual normalized configurations.
The anchor determines the real center and positive radius. Only explicit open
positional inequalities enter the small-cluster hypothesis.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryClusterReconstruction

open Configuration

variable {n m : ℕ} {i a : Fin n} {S : Finset (Fin n)} {l u : Fin (m + 1)}

/-- Explicit positional smallness, with no configuration or shape hypotheses hidden inside. -/
def SmallCluster (S : Finset (Fin n)) (a : Fin n) (l u : Fin (m + 1))
    (p : (Fin n ⊕ Fin m) → ℂ) : Prop :=
  (∀ j : Fin m, j.val < l.val → (p (Sum.inr j)).re < (p (Sum.inl a)).re) ∧
    (∀ j : Fin m, u.val ≤ j.val → (p (Sum.inl a)).re < (p (Sum.inr j)).re) ∧
    (∀ j ∈ S, ∀ k, k ∉ S →
      ‖p (Sum.inl j) - ((p (Sum.inl a)).re : ℂ)‖ <
        ‖((p (Sum.inl a)).re : ℂ) - p (Sum.inl k)‖) ∧
    (∀ j ∈ boundaryClusterBlock l u, ∀ k, k ∉ boundaryClusterBlock l u →
      |(p (Sum.inr j)).re - (p (Sum.inl a)).re| <
        |(p (Sum.inr k)).re - (p (Sum.inl a)).re|)

/-- The anchor's real coordinate is the collision center. -/
def center (c : Normalized i m) (a : Fin n) : ℝ := (c.val.interior a : ℂ).re

/-- The anchor's positive height is the collision radius. -/
def radius (c : Normalized i m) (a : Fin n) : ℝ := (c.val.interior a : ℂ).im

theorem radius_pos (c : Normalized i m) (a : Fin n) : 0 < radius c a :=
  (c.val.interior a).im_pos

def base (c : Normalized i m) (S : Finset (Fin n)) (a j : Fin n) : ℂ :=
  if j ∈ S then (center c a : ℂ) else (c.val.interior j : ℂ)

def velocity (c : Normalized i m) (S : Finset (Fin n)) (a j : Fin n) : ℂ :=
  if j ∈ S then ((c.val.interior j : ℂ) - (center c a : ℂ)) / (radius c a : ℂ) else 0

def boundaryBase (c : Normalized i m) (a : Fin n) (l u : Fin (m + 1)) (j : Fin m) : ℝ :=
  if j ∈ boundaryClusterBlock l u then center c a else c.val.boundary j

def boundaryVelocity (c : Normalized i m) (a : Fin n) (l u : Fin (m + 1)) (j : Fin m) : ℝ :=
  if j ∈ boundaryClusterBlock l u then (c.val.boundary j - center c a) / radius c a else 0

theorem small_left (c : Normalized i m) (hsmall : SmallCluster S a l u c.val.vertexPoint)
    (j : Fin m) (hj : j.val < l.val) : c.val.boundary j < center c a := by
  simpa only [center, vertexPoint, Sum.elim_inl, Sum.elim_inr, Complex.ofReal_re] using hsmall.1 j hj

theorem small_right (c : Normalized i m) (hsmall : SmallCluster S a l u c.val.vertexPoint)
    (j : Fin m) (hj : u.val ≤ j.val) : center c a < c.val.boundary j := by
  simpa only [center, vertexPoint, Sum.elim_inl, Sum.elim_inr, Complex.ofReal_re] using hsmall.2.1 j hj

theorem boundaryBase_lt (c : Normalized i m) (hsmall : SmallCluster S a l u c.val.vertexPoint)
    (j k : Fin m) (hjk : j < k)
    (hblock : ¬(j ∈ boundaryClusterBlock l u ∧ k ∈ boundaryClusterBlock l u)) :
    boundaryBase c a l u j < boundaryBase c a l u k := by
  by_cases hj : j ∈ boundaryClusterBlock l u
  · have hk : k ∉ boundaryClusterBlock l u := fun hk => hblock ⟨hj, hk⟩
    have hkright : u.val ≤ k.val := by
      have hj' := (mem_boundaryClusterBlock l u j).mp hj
      have hk' : ¬(l.val ≤ k.val ∧ k.val < u.val) := by simpa using hk
      have hlt : j.val < k.val := hjk
      omega
    simpa only [boundaryBase, if_pos hj, if_neg hk] using small_right c hsmall k hkright
  · by_cases hk : k ∈ boundaryClusterBlock l u
    · have hjleft : j.val < l.val := by
        have hk' := (mem_boundaryClusterBlock l u k).mp hk
        have hj' : ¬(l.val ≤ j.val ∧ j.val < u.val) := by simpa using hj
        have hlt : j.val < k.val := hjk
        omega
      simpa only [boundaryBase, if_neg hj, if_pos hk] using small_left c hsmall j hjleft
    · simpa only [boundaryBase, if_neg hj, if_neg hk] using c.val.boundary_strictMono hjk

theorem velocity_im_pos (c : Normalized i m) (j : Fin n) (hj : j ∈ S) :
    0 < (velocity c S a j).im := by
  simp only [velocity, if_pos hj, Complex.div_ofReal_im, Complex.sub_im, Complex.ofReal_im, sub_zero]
  exact div_pos (c.val.interior j).im_pos (radius_pos c a)

theorem velocity_injective_on (c : Normalized i m) (j k : Fin n)
    (hj : j ∈ S) (hk : k ∈ S) (hvel : velocity c S a j = velocity c S a k) : j = k := by
  have hr : (radius c a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (radius_pos c a).ne'
  have hnum := congrArg (fun z : ℂ => z * (radius c a : ℂ)) hvel
  simp only [velocity, if_pos hj, if_pos hk, div_mul_cancel₀ _ hr] at hnum
  apply c.val.interior_injective
  apply UpperHalfPlane.ext
  simpa only [sub_add_cancel] using congrArg (fun z : ℂ => z + (center c a : ℂ)) hnum

theorem velocity_anchor (c : Normalized i m) (ha : a ∈ S) : velocity c S a a = Complex.I := by
  have hr : (radius c a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (radius_pos c a).ne'
  have hnum : (c.val.interior a : ℂ) - (center c a : ℂ) = (radius c a : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [center, radius]
  rw [velocity, if_pos ha, hnum, mul_comm, mul_div_cancel_right₀ _ hr]

/-- Actual real-cluster data reconstructed by the anchor's real part and height. -/
def datum (c : Normalized i m) (ha : a ∈ S) (hi : i ∉ S) (hcut : l ≤ u)
    (hsmall : SmallCluster S a l u c.val.vertexPoint) : BoundaryClusterData i a m S l u where
  center := center c a
  base := base c S a
  velocity := velocity c S a
  boundaryBase := boundaryBase c a l u
  boundaryVelocity := boundaryVelocity c a l u
  anchor_mem := ha
  normalized_not_mem := hi
  block_order := hcut
  base_eq_center := by intro j hj; simp [base, hj]
  base_im_pos_off := by intro j hj; simpa [base, hj] using (c.val.interior j).im_pos
  base_injective_off := by
    intro j k hj hk h
    apply c.val.interior_injective
    apply UpperHalfPlane.ext
    simpa only [base, if_neg hj, if_neg hk] using h
  base_normalized := by
    simpa [base, hi] using congrArg (fun z : UpperHalfPlane => (z : ℂ)) c.property
  velocity_im_pos := velocity_im_pos c
  velocity_zero_off := by intro j hj; simp [velocity, hj]
  velocity_injective_on := velocity_injective_on c
  velocity_anchor := velocity_anchor c ha
  boundaryBase_eq_center := by intro j hj; simp [boundaryBase, hj]
  boundaryBase_lt_center := by
    intro j hj
    have hnot : j ∉ boundaryClusterBlock l u := by
      simp only [mem_boundaryClusterBlock]
      omega
    simpa only [boundaryBase, if_neg hnot] using small_left c hsmall j hj
  center_lt_boundaryBase := by
    intro j hj
    have hnot : j ∉ boundaryClusterBlock l u := by
      simp only [mem_boundaryClusterBlock]
      omega
    simpa only [boundaryBase, if_neg hnot] using small_right c hsmall j hj
  boundaryBase_lt := boundaryBase_lt c hsmall
  boundaryVelocity_zero_off := by intro j hj; simp [boundaryVelocity, hj]
  boundaryVelocity_strictMono_on := by
    intro j k hj hk hjk
    simp only [boundaryVelocity, if_pos hj, if_pos hk]
    exact div_lt_div_of_pos_right (sub_lt_sub_right (c.val.boundary_strictMono hjk) _) (radius_pos c a)

theorem scale_mul_norm_velocity (c : Normalized i m) (j : Fin n) (hj : j ∈ S) :
    radius c a * ‖velocity c S a j‖ = ‖(c.val.interior j : ℂ) - (center c a : ℂ)‖ := by
  have hr := radius_pos c a
  simp only [velocity, if_pos hj, norm_div, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_pos hr]
  exact mul_div_cancel₀ _ hr.ne'

theorem scale_mul_abs_boundaryVelocity (c : Normalized i m) (j : Fin m)
    (hj : j ∈ boundaryClusterBlock l u) :
    radius c a * |boundaryVelocity c a l u j| = |c.val.boundary j - center c a| := by
  have hr := radius_pos c a
  simp only [boundaryVelocity, if_pos hj, abs_div]
  rw [abs_of_pos hr]
  exact mul_div_cancel₀ _ hr.ne'

theorem scaled_interior (c : Normalized i m) (j : Fin n) :
    base c S a j + (radius c a : ℂ) * velocity c S a j = (c.val.interior j : ℂ) := by
  have hr : (radius c a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (radius_pos c a).ne'
  by_cases hj : j ∈ S
  · simp only [base, velocity, if_pos hj]
    rw [mul_comm (radius c a : ℂ), div_mul_cancel₀ _ hr]
    abel
  · simp [base, velocity, hj]

theorem scaled_boundary (c : Normalized i m) (j : Fin m) :
    boundaryBase c a l u j + radius c a * boundaryVelocity c a l u j = c.val.boundary j := by
  have hr : radius c a ≠ 0 := (radius_pos c a).ne'
  by_cases hj : j ∈ boundaryClusterBlock l u
  · simp only [boundaryBase, boundaryVelocity, if_pos hj]
    rw [mul_comm (radius c a), div_mul_cancel₀ _ hr]
    abel
  · simp [boundaryBase, boundaryVelocity, hj]

theorem small_interior (c : Normalized i m) (hsmall : SmallCluster S a l u c.val.vertexPoint)
    (j : Fin n) (hj : j ∈ S) (k : Fin n) (hk : k ∉ S) :
    ‖(c.val.interior j : ℂ) - (center c a : ℂ)‖ <
      ‖(center c a : ℂ) - (c.val.interior k : ℂ)‖ := by
  simpa only [center, vertexPoint, Sum.elim_inl] using hsmall.2.2.1 j hj k hk

theorem small_boundary (c : Normalized i m) (hsmall : SmallCluster S a l u c.val.vertexPoint)
    (j : Fin m) (hj : j ∈ boundaryClusterBlock l u) (k : Fin m)
    (hk : k ∉ boundaryClusterBlock l u) :
    |c.val.boundary j - center c a| < |c.val.boundary k - center c a| := by
  simpa only [center, vertexPoint, Sum.elim_inl, Sum.elim_inr, Complex.ofReal_re] using
    hsmall.2.2.2 j hj k hk

/-- The explicit positional bounds imply the actual scale admissibility conditions. -/
theorem admissibleScale_datum (c : Normalized i m) (ha : a ∈ S) (hi : i ∉ S) (hcut : l ≤ u)
    (hsmall : SmallCluster S a l u c.val.vertexPoint) :
    (datum c ha hi hcut hsmall).AdmissibleScale (radius c a) := by
  refine ⟨(radius_pos c a).le, fun j k hjk => ?_, fun j k hjk hblock => ?_⟩
  · change radius c a * ‖velocity c S a j - velocity c S a k‖ < ‖base c S a j - base c S a k‖
    change base c S a j ≠ base c S a k at hjk
    by_cases hj : j ∈ S
    · by_cases hk : k ∈ S
      · exact (hjk (by simp [base, hj, hk])).elim
      · have hvk : velocity c S a k = 0 := by simp [velocity, hk]
        rw [hvk, sub_zero, scale_mul_norm_velocity c j hj]
        simpa only [base, if_pos hj, if_neg hk] using small_interior c hsmall j hj k hk
    · by_cases hk : k ∈ S
      · have hvj : velocity c S a j = 0 := by simp [velocity, hj]
        rw [hvj, zero_sub, norm_neg, scale_mul_norm_velocity c k hk]
        simpa only [base, if_neg hj, if_pos hk, norm_sub_rev] using small_interior c hsmall k hk j hj
      · have hvj : velocity c S a j = 0 := by simp [velocity, hj]
        have hvk : velocity c S a k = 0 := by simp [velocity, hk]
        rw [hvj, hvk, sub_self, norm_zero, mul_zero]
        exact norm_pos_iff.mpr (sub_ne_zero.mpr hjk)
  · change radius c a * |boundaryVelocity c a l u k - boundaryVelocity c a l u j| <
      boundaryBase c a l u k - boundaryBase c a l u j
    by_cases hj : j ∈ boundaryClusterBlock l u
    · have hk : k ∉ boundaryClusterBlock l u := fun hk => hblock ⟨hj, hk⟩
      have hvk : boundaryVelocity c a l u k = 0 := by simp [boundaryVelocity, hk]
      rw [hvk, zero_sub, abs_neg, scale_mul_abs_boundaryVelocity c j hj]
      have hright : center c a < c.val.boundary k := by
        simpa only [boundaryBase, if_pos hj, if_neg hk] using boundaryBase_lt c hsmall j k hjk hblock
      have hs := small_boundary c hsmall j hj k hk
      rw [abs_of_pos (sub_pos.mpr hright)] at hs
      simpa only [boundaryBase, if_pos hj, if_neg hk] using hs
    · by_cases hk : k ∈ boundaryClusterBlock l u
      · have hvj : boundaryVelocity c a l u j = 0 := by simp [boundaryVelocity, hj]
        rw [hvj, sub_zero, scale_mul_abs_boundaryVelocity c k hk]
        have hleft : c.val.boundary j < center c a := by
          simpa only [boundaryBase, if_neg hj, if_pos hk] using boundaryBase_lt c hsmall j k hjk hblock
        have hs := small_boundary c hsmall k hk j hj
        rw [abs_of_neg (sub_neg.mpr hleft), neg_sub] at hs
        simpa only [boundaryBase, if_neg hj, if_pos hk] using hs
      · have hvj : boundaryVelocity c a l u j = 0 := by simp [boundaryVelocity, hj]
        have hvk : boundaryVelocity c a l u k = 0 := by simp [boundaryVelocity, hk]
        rw [hvj, hvk, sub_self, abs_zero, mul_zero]
        exact sub_pos.mpr (boundaryBase_lt c hsmall j k hjk hblock)

/-- Actual admissible boundary-cluster parameters extracted from the normalized configuration. -/
def domain (c : Normalized i m) (ha : a ∈ S) (hi : i ∉ S) (hcut : l ≤ u)
    (hsmall : SmallCluster S a l u c.val.vertexPoint) : BoundaryClusterDomain i a m S l u :=
  ⟨(datum c ha hi hcut hsmall, radius c a), admissibleScale_datum c ha hi hcut hsmall⟩

/-- Reinsertion of the reconstructed data recovers the original compactified configuration. -/
theorem insertion_domain (c : Normalized i m) (ha : a ∈ S) (hi : i ∉ S) (hcut : l ≤ u)
    (hsmall : SmallCluster S a l u c.val.vertexPoint) :
    (domain c ha hi hcut hsmall).insertion = compactificationEmbedding i c := by
  let x := domain c ha hi hcut hsmall
  change x.insertion = compactificationEmbedding i c
  rw [BoundaryClusterDomain.insertion_pos x (radius_pos c a)]
  apply congrArg (compactificationEmbedding i)
  apply Subtype.ext
  apply Configuration.ext
  · funext j
    apply UpperHalfPlane.ext
    exact scaled_interior c j
  · funext j
    exact scaled_boundary c j

end EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryClusterReconstruction
