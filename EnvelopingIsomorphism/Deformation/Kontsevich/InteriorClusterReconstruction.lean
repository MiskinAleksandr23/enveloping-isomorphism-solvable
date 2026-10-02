import EnvelopingIsomorphism.Deformation.Kontsevich.InteriorClusterEmbedding

/-!
# Reconstructing cluster parameters from an actual configuration

The chosen labels give the actual center `z_a` and radius `|z_b-z_a|`.
Inside-cluster velocities are `(z_j-z_a)/radius`; outside velocities are zero.
Explicit small-displacement inequalities imply that these reconstructed data
belong to the admissible normalized slice and reinsert as the original configuration.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich

open Configuration

namespace ClusterReconstruction

variable {n m : ℕ} {i : Fin n} {S : Finset (Fin n)} {a b : Fin n}

def radius (c : Normalized i m) (a b : Fin n) : ℝ :=
  ‖(c.val.interior b : ℂ) - (c.val.interior a : ℂ)‖

theorem radius_pos (c : Normalized i m) (hba : b ≠ a) : 0 < radius c a b :=
  norm_pos_iff.mpr (sub_ne_zero.mpr (fun h => hba (c.val.interior_injective (UpperHalfPlane.ext h))))

def base (c : Normalized i m) (S : Finset (Fin n)) (a j : Fin n) : UpperHalfPlane :=
  if j ∈ S then c.val.interior a else c.val.interior j

def velocity (c : Normalized i m) (S : Finset (Fin n)) (a b j : Fin n) : ℂ :=
  if j ∈ S then ((c.val.interior j : ℂ) - (c.val.interior a : ℂ)) / (radius c a b : ℂ) else 0

theorem base_eq_iff (c : Normalized i m) (ha : a ∈ S) (j k : Fin n) :
    base c S a j = base c S a k ↔ j = k ∨ (j ∈ S ∧ k ∈ S) := by
  constructor
  · intro h
    by_cases hj : j ∈ S
    · by_cases hk : k ∈ S
      · exact Or.inr ⟨hj, hk⟩
      · have heq : a = k := c.val.interior_injective (by simpa [base, hj, hk] using h)
        exact False.elim (hk (heq ▸ ha))
    · by_cases hk : k ∈ S
      · have heq : j = a := c.val.interior_injective (by simpa [base, hj, hk] using h)
        exact False.elim (hj (heq.symm ▸ ha))
      · exact Or.inl (c.val.interior_injective (by simpa [base, hj, hk] using h))
  · rintro (rfl | ⟨hj, hk⟩)
    · rfl
    · simp [base, hj, hk]

theorem separated (c : Normalized i m) (ha : a ∈ S) (hba : b ≠ a) (j k : Fin n)
    (hbase : base c S a j = base c S a k) (hv : velocity c S a b j = velocity c S a b k) : j = k := by
  rcases (base_eq_iff c ha j k).mp hbase with heq | ⟨hj, hk⟩
  · exact heq
  · have hr : (radius c a b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (radius_pos c hba).ne'
    have hnum := congrArg (fun z : ℂ => z * (radius c a b : ℂ)) hv
    simp only [velocity, if_pos hj, if_pos hk, div_mul_cancel₀ _ hr] at hnum
    apply c.val.interior_injective
    apply UpperHalfPlane.ext
    simpa only [sub_add_cancel] using congrArg (fun z : ℂ => z + (c.val.interior a : ℂ)) hnum

/-- Actual normalized cluster data extracted from a distinct-point configuration. -/
def datum (c : Normalized i m) (ha : a ∈ S) (hba : b ≠ a) (hanchor : i ∈ S → a = i) :
    SingleInteriorCluster i m S where
  base := base c S a
  velocity := velocity c S a b
  separated := separated c ha hba
  boundary := c.val.boundary
  boundary_strictMono := c.val.boundary_strictMono
  base_normalized := by
    by_cases hi : i ∈ S
    · simpa [base, hi, hanchor hi] using c.property
    · simpa [base, hi] using c.property
  velocity_normalized := by
    by_cases hi : i ∈ S
    · simp [velocity, hi, hanchor hi]
    · simp [velocity, hi]
  cluster_nonempty := ⟨a, ha⟩
  base_eq_iff := base_eq_iff c ha
  velocity_zero_off := by intro j hj; simp [velocity, hj]

theorem velocity_anchor (c : Normalized i m) (ha : a ∈ S) : velocity c S a b a = 0 := by
  simp [velocity, ha]

theorem norm_velocity_reference (c : Normalized i m) (hb : b ∈ S) (hba : b ≠ a) :
    ‖velocity c S a b b‖ = 1 := by
  have hr := radius_pos c hba
  simp only [velocity, if_pos hb, norm_div, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_pos hr]
  exact div_self hr.ne'

theorem scale_mul_norm_velocity (c : Normalized i m) (hba : b ≠ a) (j : Fin n) (hj : j ∈ S) :
    radius c a b * ‖velocity c S a b j‖ = ‖(c.val.interior j : ℂ) - (c.val.interior a : ℂ)‖ := by
  have hr := radius_pos c hba
  simp only [velocity, if_pos hj, norm_div, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_pos hr]
  exact mul_div_cancel₀ _ hr.ne'

theorem scaled_position (c : Normalized i m) (hba : b ≠ a) (j : Fin n) :
    (base c S a j : ℂ) + (radius c a b : ℂ) * velocity c S a b j = (c.val.interior j : ℂ) := by
  have hr : (radius c a b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (radius_pos c hba).ne'
  by_cases hj : j ∈ S
  · simp only [base, velocity, if_pos hj]
    rw [mul_comm (radius c a b : ℂ), div_mul_cancel₀ _ hr]
    abel
  · simp [base, velocity, hj]

/-- Open positional inequalities saying the cluster is smaller than its distance
to the real boundary and to every outside interior point. -/
def SmallCluster (S : Finset (Fin n)) (a : Fin n) (p : (Fin n ⊕ Fin m) → ℂ) : Prop :=
  (∀ j ∈ S, ‖p (Sum.inl j) - p (Sum.inl a)‖ < (p (Sum.inl a)).im) ∧
    (∀ j ∈ S, ∀ k, k ∉ S →
      ‖p (Sum.inl j) - p (Sum.inl a)‖ < ‖p (Sum.inl a) - p (Sum.inl k)‖)

theorem admissibleScale_datum (c : Normalized i m) (ha : a ∈ S) (hba : b ≠ a)
    (hanchor : i ∈ S → a = i) (hsmall : SmallCluster S a c.val.vertexPoint) :
    (datum c ha hba hanchor).toInteriorCollisionData.AdmissibleScale (radius c a b) := by
  refine ⟨(radius_pos c hba).le, fun j => ?_, fun j k hjk => ?_⟩
  · change radius c a b * ‖velocity c S a b j‖ < (base c S a j).im
    by_cases hj : j ∈ S
    · rw [scale_mul_norm_velocity c hba j hj]
      simpa only [base, if_pos hj, vertexPoint, Sum.elim_inl, UpperHalfPlane.coe_im] using hsmall.1 j hj
    · simpa [velocity, base, hj] using (c.val.interior j).im_pos
  · change radius c a b * ‖velocity c S a b j - velocity c S a b k‖ <
      ‖(base c S a j : ℂ) - (base c S a k : ℂ)‖
    change base c S a j ≠ base c S a k at hjk
    by_cases hj : j ∈ S
    · by_cases hk : k ∈ S
      · exact False.elim (hjk (by simp [base, hj, hk]))
      · have hvk : velocity c S a b k = 0 := by simp [velocity, hk]
        rw [hvk, sub_zero, scale_mul_norm_velocity c hba j hj]
        simpa only [base, if_pos hj, if_neg hk, vertexPoint, Sum.elim_inl] using hsmall.2 j hj k hk
    · by_cases hk : k ∈ S
      · have hvj : velocity c S a b j = 0 := by simp [velocity, hj]
        rw [hvj, zero_sub, norm_neg, scale_mul_norm_velocity c hba k hk]
        simpa only [base, if_neg hj, if_pos hk, norm_sub_rev, vertexPoint, Sum.elim_inl] using hsmall.2 k hk j hj
      · have hvj : velocity c S a b j = 0 := by simp [velocity, hj]
        have hvk : velocity c S a b k = 0 := by simp [velocity, hk]
        rw [hvj, hvk, sub_self, norm_zero, mul_zero]
        exact norm_pos_iff.mpr (sub_ne_zero.mpr (fun h => hjk (UpperHalfPlane.ext h)))

/-- The actual normalized cluster parameters of every sufficiently small configuration. -/
def slice (c : Normalized i m) (ha : a ∈ S) (hb : b ∈ S) (hba : b ≠ a)
    (hanchor : i ∈ S → a = i) (hsmall : SmallCluster S a c.val.vertexPoint) :
    NormalizedInteriorClusterSlice i m S a b :=
  ⟨⟨(datum c ha hba hanchor, radius c a b), admissibleScale_datum c ha hba hanchor hsmall⟩,
    velocity_anchor c ha, norm_velocity_reference c hb hba⟩

/-- Reinsertion of these reconstructed parameters is exactly the original point of the compactification. -/
theorem insertion_slice (c : Normalized i m) (ha : a ∈ S) (hb : b ∈ S) (hba : b ≠ a)
    (hanchor : i ∈ S → a = i) (hsmall : SmallCluster S a c.val.vertexPoint) :
    (slice c ha hb hba hanchor hsmall).insertion = compactificationEmbedding i c := by
  let x := slice c ha hb hba hanchor hsmall
  change x.val.insertion = compactificationEmbedding i c
  rw [InteriorClusterDomain.insertion_pos x.val (radius_pos c hba)]
  apply congrArg (compactificationEmbedding i)
  apply Subtype.ext
  apply Configuration.ext
  · funext j
    apply UpperHalfPlane.ext
    exact scaled_position c hba j
  · rfl

end ClusterReconstruction

end EnvelopingIsomorphism.Deformation.Kontsevich
