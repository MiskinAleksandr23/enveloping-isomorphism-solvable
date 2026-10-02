import EnvelopingIsomorphism.Deformation.Kontsevich.PureBoundaryClusterDomain

/-! Reconstruction of actual pure external-cluster parameters from original
normalized configurations. The left endpoint is the center and the positive
endpoint gap is the radius. Explicit positional smallness supplies all safe
scale bounds; no reconstructed datum or insertion equality is assumed. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.PureBoundaryClusterReconstruction

open Configuration

variable {n m : ℕ} {i : Fin n} {l u : Fin (m + 1)} {a b : Fin m}

def SmallCluster (a : Fin m) (l u : Fin (m + 1)) (p : (Fin n ⊕ Fin m) → ℂ) : Prop :=
  ∀ j ∈ boundaryClusterBlock l u, ∀ k, k ∉ boundaryClusterBlock l u →
    |(p (Sum.inr j)).re - (p (Sum.inr a)).re| <
      |(p (Sum.inr k)).re - (p (Sum.inr a)).re|

def center (c : Normalized i m) (a : Fin m) : ℝ := c.val.boundary a

def radius (c : Normalized i m) (a b : Fin m) : ℝ := c.val.boundary b - c.val.boundary a

theorem radius_pos (c : Normalized i m) (hab : a < b) : 0 < radius c a b :=
  sub_pos.mpr (c.val.boundary_strictMono hab)

theorem mem_block_iff (hleft : a.val = l.val) (hright : b.val + 1 = u.val) (j : Fin m) :
    j ∈ boundaryClusterBlock l u ↔ a ≤ j ∧ j ≤ b := by
  rw [mem_boundaryClusterBlock]
  change (l.val ≤ j.val ∧ j.val < u.val) ↔ (a.val ≤ j.val ∧ j.val ≤ b.val)
  omega

theorem left_mem (hleft : a.val = l.val) (hright : b.val + 1 = u.val) (hab : a < b) :
    a ∈ boundaryClusterBlock l u :=
  (mem_block_iff hleft hright a).mpr ⟨le_rfl, hab.le⟩

theorem right_mem (hleft : a.val = l.val) (hright : b.val + 1 = u.val) (hab : a < b) :
    b ∈ boundaryClusterBlock l u :=
  (mem_block_iff hleft hright b).mpr ⟨hab.le, le_rfl⟩

def boundaryBase (c : Normalized i m) (a : Fin m) (l u : Fin (m + 1)) (j : Fin m) : ℝ :=
  if j ∈ boundaryClusterBlock l u then center c a else c.val.boundary j

def boundaryVelocity (c : Normalized i m) (a b : Fin m) (l u : Fin (m + 1)) (j : Fin m) : ℝ :=
  if j ∈ boundaryClusterBlock l u then (c.val.boundary j - center c a) / radius c a b else 0

theorem left_gap (c : Normalized i m) (hleft : a.val = l.val)
    (j : Fin m) (hj : j.val < l.val) : c.val.boundary j < center c a := by
  apply c.val.boundary_strictMono
  change j.val < a.val
  omega

theorem right_gap (c : Normalized i m) (hright : b.val + 1 = u.val) (hab : a < b)
    (j : Fin m) (hj : u.val ≤ j.val) : center c a < c.val.boundary j := by
  apply c.val.boundary_strictMono
  change a.val < j.val
  have hab' : a.val < b.val := hab
  omega

theorem boundaryBase_lt (c : Normalized i m) (hleft : a.val = l.val)
    (hright : b.val + 1 = u.val) (hab : a < b)
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
    simpa only [boundaryBase, if_pos hj, if_neg hk] using right_gap c hright hab k hkright
  · by_cases hk : k ∈ boundaryClusterBlock l u
    · have hjleft : j.val < l.val := by
        have hk' := (mem_boundaryClusterBlock l u k).mp hk
        have hj' : ¬(l.val ≤ j.val ∧ j.val < u.val) := by simpa using hj
        have hlt : j.val < k.val := hjk
        omega
      simpa only [boundaryBase, if_neg hj, if_pos hk] using left_gap c hleft j hjleft
    · simpa only [boundaryBase, if_neg hj, if_neg hk] using c.val.boundary_strictMono hjk

/-- The native original configuration supplies every primitive datum condition. -/
def datum (c : Normalized i m) (hleft : a.val = l.val) (hright : b.val + 1 = u.val)
    (hab : a < b) : PureBoundaryClusterData i m l u a b where
  center := center c a
  interior := c.val.interior
  boundaryBase := boundaryBase c a l u
  boundaryVelocity := boundaryVelocity c a b l u
  left_endpoint := hleft
  right_endpoint := hright
  endpoint_lt := hab
  interior_injective := c.val.interior_injective
  interior_normalized := c.property
  boundaryBase_eq_center := by intro j hj; simp [boundaryBase, hj]
  boundaryBase_lt_center := by
    intro j hj
    have hnot : j ∉ boundaryClusterBlock l u := by
      simp only [mem_boundaryClusterBlock]
      omega
    simpa only [boundaryBase, if_neg hnot] using left_gap c hleft j hj
  center_lt_boundaryBase := by
    intro j hj
    have hnot : j ∉ boundaryClusterBlock l u := by
      simp only [mem_boundaryClusterBlock]
      omega
    simpa only [boundaryBase, if_neg hnot] using right_gap c hright hab j hj
  boundaryBase_lt := boundaryBase_lt c hleft hright hab
  boundaryVelocity_zero_off := by intro j hj; simp [boundaryVelocity, hj]
  boundaryVelocity_strictMono_on := by
    intro j k hj hk hjk
    simp only [boundaryVelocity, if_pos hj, if_pos hk]
    exact div_lt_div_of_pos_right (sub_lt_sub_right (c.val.boundary_strictMono hjk) _) (radius_pos c hab)
  boundaryVelocity_left := by
    simp [boundaryVelocity, left_mem hleft hright hab, center]
  boundaryVelocity_right := by
    simp only [boundaryVelocity, if_pos (right_mem hleft hright hab), center, radius]
    exact div_self (radius_pos c hab).ne'

theorem scale_mul_abs_boundaryVelocity (c : Normalized i m) (hab : a < b) (j : Fin m)
    (hj : j ∈ boundaryClusterBlock l u) :
    radius c a b * |boundaryVelocity c a b l u j| = |c.val.boundary j - center c a| := by
  have hr := radius_pos c hab
  simp only [boundaryVelocity, if_pos hj, abs_div]
  rw [abs_of_pos hr]
  exact mul_div_cancel₀ _ hr.ne'

theorem scaled_boundary (c : Normalized i m) (hab : a < b) (j : Fin m) :
    boundaryBase c a l u j + radius c a b * boundaryVelocity c a b l u j = c.val.boundary j := by
  have hr : radius c a b ≠ 0 := (radius_pos c hab).ne'
  by_cases hj : j ∈ boundaryClusterBlock l u
  · simp only [boundaryBase, boundaryVelocity, if_pos hj]
    rw [mul_comm (radius c a b), div_mul_cancel₀ _ hr]
    abel
  · simp [boundaryBase, boundaryVelocity, hj]

theorem small_boundary (c : Normalized i m) (hsmall : SmallCluster a l u c.val.vertexPoint)
    (j : Fin m) (hj : j ∈ boundaryClusterBlock l u) (k : Fin m)
    (hk : k ∉ boundaryClusterBlock l u) :
    |c.val.boundary j - center c a| < |c.val.boundary k - center c a| := by
  simpa only [center, vertexPoint, Sum.elim_inr, Complex.ofReal_re] using hsmall j hj k hk

/-- The explicit positional comparison proves the actual admissible-scale inequalities. -/
theorem admissibleScale_datum (c : Normalized i m) (hleft : a.val = l.val)
    (hright : b.val + 1 = u.val) (hab : a < b)
    (hsmall : SmallCluster a l u c.val.vertexPoint) :
    (datum c hleft hright hab).AdmissibleScale (radius c a b) := by
  refine ⟨(radius_pos c hab).le, fun j k hjk hblock => ?_⟩
  change radius c a b * |boundaryVelocity c a b l u k - boundaryVelocity c a b l u j| <
    boundaryBase c a l u k - boundaryBase c a l u j
  by_cases hj : j ∈ boundaryClusterBlock l u
  · have hk : k ∉ boundaryClusterBlock l u := fun hk => hblock ⟨hj, hk⟩
    have hvk : boundaryVelocity c a b l u k = 0 := by simp [boundaryVelocity, hk]
    rw [hvk, zero_sub, abs_neg, scale_mul_abs_boundaryVelocity c hab j hj]
    have hright' : center c a < c.val.boundary k := by
      simpa only [boundaryBase, if_pos hj, if_neg hk] using boundaryBase_lt c hleft hright hab j k hjk hblock
    have hs := small_boundary c hsmall j hj k hk
    rw [abs_of_pos (sub_pos.mpr hright')] at hs
    simpa only [boundaryBase, if_pos hj, if_neg hk] using hs
  · by_cases hk : k ∈ boundaryClusterBlock l u
    · have hvj : boundaryVelocity c a b l u j = 0 := by simp [boundaryVelocity, hj]
      rw [hvj, sub_zero, scale_mul_abs_boundaryVelocity c hab k hk]
      have hleft' : c.val.boundary j < center c a := by
        simpa only [boundaryBase, if_neg hj, if_pos hk] using boundaryBase_lt c hleft hright hab j k hjk hblock
      have hs := small_boundary c hsmall k hk j hj
      rw [abs_of_neg (sub_neg.mpr hleft'), neg_sub] at hs
      simpa only [boundaryBase, if_neg hj, if_pos hk] using hs
    · have hvj : boundaryVelocity c a b l u j = 0 := by simp [boundaryVelocity, hj]
      have hvk : boundaryVelocity c a b l u k = 0 := by simp [boundaryVelocity, hk]
      rw [hvj, hvk, sub_self, abs_zero, mul_zero]
      exact sub_pos.mpr (boundaryBase_lt c hleft hright hab j k hjk hblock)

def domain (c : Normalized i m) (hleft : a.val = l.val) (hright : b.val + 1 = u.val) (hab : a < b)
    (hsmall : SmallCluster a l u c.val.vertexPoint) : PureBoundaryClusterDomain i m l u a b :=
  ⟨(datum c hleft hright hab, radius c a b), admissibleScale_datum c hleft hright hab hsmall⟩

/-- Reinsertion gives exactly the original encoded configuration. -/
theorem insertion_domain (c : Normalized i m) (hleft : a.val = l.val)
    (hright : b.val + 1 = u.val) (hab : a < b) (hsmall : SmallCluster a l u c.val.vertexPoint) :
    (domain c hleft hright hab hsmall).insertion = compactificationEmbedding i c := by
  let x := domain c hleft hright hab hsmall
  change x.insertion = compactificationEmbedding i c
  rw [PureBoundaryClusterDomain.insertion_pos x (radius_pos c hab)]
  apply congrArg (compactificationEmbedding i)
  apply Subtype.ext
  apply Configuration.ext
  · rfl
  · funext j
    exact scaled_boundary c hab j

end EnvelopingIsomorphism.Deformation.Kontsevich.PureBoundaryClusterReconstruction
