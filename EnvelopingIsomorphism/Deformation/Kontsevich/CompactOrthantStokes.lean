import EnvelopingIsomorphism.Deformation.Kontsevich.CompactSupportBoxes

/-! Stokes on a coordinate orthant for a compactly supported C1 form.
The proof localizes to one actual finite box. Artificial box faces vanish;
only the oriented lower faces belonging to the orthant remain. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.CompactOrthantStokes

open Set MeasureTheory BoxIntegral ContinuousAlternatingMap
open BoxStokes

/-- An arbitrary coordinate orthant, allowing unconstrained coordinates. -/
def orthant {d : ℕ} (S : Finset (Fin d)) : Set (Coord d) :=
  {x | ∀ i ∈ S, 0 ≤ x i}

@[simp] theorem mem_orthant {d : ℕ} (S : Finset (Fin d)) (x : Coord d) :
    x ∈ orthant S ↔ ∀ i ∈ S, 0 ≤ x i := Iff.rfl

@[simp] theorem orthant_empty (d : ℕ) : orthant (∅ : Finset (Fin d)) = Set.univ := by
  ext x
  simp [orthant]

theorem measurableSet_orthant {d : ℕ} (S : Finset (Fin d)) : MeasurableSet (orthant S) := by
  have h : orthant S = ⋂ i ∈ S, {x : Coord d | 0 ≤ x i} := by ext x; simp [orthant]
  rw [h]
  exact MeasurableSet.biInter S.countable_toSet (fun i hi ↦ measurableSet_le measurable_const (measurable_pi_apply i))

/-- The remaining constrained coordinates on the face with coordinate i removed. -/
def faceIndices {n : ℕ} (S : Finset (Fin (n + 1))) (i : Fin (n + 1)) : Finset (Fin n) :=
  Finset.univ.filter fun j ↦ i.succAbove j ∈ S

@[simp] theorem mem_faceIndices {n : ℕ} (S : Finset (Fin (n + 1))) (i : Fin (n + 1)) (j : Fin n) :
    j ∈ faceIndices S i ↔ i.succAbove j ∈ S := by simp [faceIndices]

theorem faceEmbedding_mem_orthant {n : ℕ} (S : Finset (Fin (n + 1)))
    (i : Fin (n + 1)) (x : Coord n) :
    faceEmbedding i 0 x ∈ orthant S ↔ x ∈ orthant (faceIndices S i) := by
  constructor
  · intro hx j hj
    have h := hx (i.succAbove j) ((mem_faceIndices S i j).mp hj)
    simpa only [faceEmbedding, Fin.insertNth_apply_succAbove] using h
  · intro hx j hj
    induction j using i.succAboveCases with
    | x => simp [faceEmbedding]
    | p j =>
      simpa only [faceEmbedding, Fin.insertNth_apply_succAbove] using
        hx j ((mem_faceIndices S i j).mpr hj)

/-- A finite truncation of the orthant, with artificial faces at ±R. -/
def coordinateBox {d : ℕ} (S : Finset (Fin d)) (R : ℝ) (hR : 0 < R) : Box (Fin d) where
  lower i := if i ∈ S then 0 else -R
  upper _ := R
  lower_lt_upper i := by split_ifs <;> linarith

@[simp] theorem coordinateBox_lower {d : ℕ} (S : Finset (Fin d)) (R : ℝ) (hR : 0 < R) (i : Fin d) :
    (coordinateBox S R hR).lower i = if i ∈ S then 0 else -R := rfl

@[simp] theorem coordinateBox_upper {d : ℕ} (S : Finset (Fin d)) (R : ℝ) (hR : 0 < R) (i : Fin d) :
    (coordinateBox S R hR).upper i = R := rfl

theorem Icc_coordinateBox_subset_orthant {d : ℕ} (S : Finset (Fin d)) (R : ℝ) (hR : 0 < R) :
    Box.Icc (coordinateBox S R hR) ⊆ orthant S := by
  intro x hx i hi
  have h := hx.1 i
  simpa only [coordinateBox_lower, if_pos hi] using h

theorem mem_Icc_coordinateBox_of_abs_lt {d : ℕ} (S : Finset (Fin d)) (R : ℝ) (hR : 0 < R)
    {x : Coord d} (hx : x ∈ orthant S) (hbound : ∀ i, |x i| < R) :
    x ∈ Box.Icc (coordinateBox S R hR) := by
  constructor
  · intro i
    change (if i ∈ S then 0 else -R) ≤ x i
    split_ifs with hi
    · exact hx i hi
    · exact (abs_lt.mp (hbound i)).1.le
  · intro i
    exact (abs_lt.mp (hbound i)).2.le

theorem coordinateBox_face {n : ℕ} (S : Finset (Fin (n + 1))) (R : ℝ) (hR : 0 < R)
    (i : Fin (n + 1)) :
    (coordinateBox S R hR).face i = coordinateBox (faceIndices S i) R hR := by
  apply Box.ext
  intro x
  simp [Box.mem_def, coordinateBox, Box.face, Function.comp_def]

/-- Localization uses actual vanishing outside the finite box. -/
theorem integral_orthant_eq_box {d : ℕ} (S : Finset (Fin d)) (R : ℝ) (hR : 0 < R)
    (f : Coord d → ℝ) (hbound : ∀ x ∈ Function.support f, ∀ i, |x i| < R) :
    (∫ x in orthant S, f x) = ∫ x in Box.Icc (coordinateBox S R hR), f x := by
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (measurableSet_orthant S)
    (Icc_coordinateBox_subset_orthant S R hR)
  rintro x ⟨hx, hn⟩
  by_contra hf
  exact hn (mem_Icc_coordinateBox_of_abs_lt S R hR hx (hbound x hf))

/-- Compact support localization also proves integrability on the unbounded orthant. -/
theorem integrableOn_orthant_of_support_bound {d : ℕ} (S : Finset (Fin d)) (R : ℝ) (hR : 0 < R)
    (f : Coord d → ℝ) (hf : Continuous f)
    (hbound : ∀ x ∈ Function.support f, ∀ i, |x i| < R) : IntegrableOn f (orthant S) := by
  apply (hf.continuousOn.integrableOn_compact (coordinateBox S R hR).isCompact_Icc).of_forall_sdiff_eq_zero
    (measurableSet_orthant S)
  rintro x ⟨hx, hn⟩
  by_contra hne
  exact hn (mem_Icc_coordinateBox_of_abs_lt S R hR hx (hbound x hne))

/-- Restricting to a coordinate face preserves the same tangential support bound. -/
theorem face_density_support_bound {n : ℕ} (ω : Form n) (R : ℝ)
    (hbound : ∀ x ∈ Function.support ω, ∀ i, |x i| < R)
    (i : Fin (n + 1)) (c : ℝ) :
    ∀ x ∈ Function.support (fun y ↦ facePullback ω i c y (standardBasis n)), ∀ j, |x j| < R := by
  intro x hx j
  have hn : ω (faceEmbedding i c x) ≠ 0 := by
    intro hz
    apply hx
    change facePullback ω i c x (standardBasis n) = 0
    rw [facePullback_standardBasis]
    change ω (faceEmbedding i c x) _ = 0
    rw [hz]
    rfl
  have h := hbound (faceEmbedding i c x) hn (i.succAbove j)
  simpa only [faceEmbedding, Fin.insertNth_apply_succAbove] using h

/-- Every face beyond the support vanishes pointwise, before integration. -/
theorem face_density_eq_zero_of_abs_ge {n : ℕ} (ω : Form n) (R : ℝ)
    (hbound : ∀ x ∈ Function.support ω, ∀ i, |x i| < R)
    (i : Fin (n + 1)) (c : ℝ) (hc : R ≤ |c|) (x : Coord n) :
    facePullback ω i c x (standardBasis n) = 0 := by
  have hω : ω (faceEmbedding i c x) = 0 := by
    by_contra hn
    have h := hbound (faceEmbedding i c x) hn i
    simp only [faceEmbedding, Fin.insertNth_apply_same] at h
    exact (not_lt_of_ge hc) h
  rw [facePullback_standardBasis]
  change ω (faceEmbedding i c x) _ = 0
  rw [hω]
  rfl

/-- The lower face integral has the same induced orthant coordinates as the box face. -/
theorem integral_lower_face_eq_box {n : ℕ} (ω : Form n) (S : Finset (Fin (n + 1)))
    (R : ℝ) (hR : 0 < R) (hbound : ∀ x ∈ Function.support ω, ∀ i, |x i| < R)
    (i : Fin (n + 1)) :
    (∫ x in orthant (faceIndices S i), facePullback ω i 0 x (standardBasis n)) =
      ∫ x in Box.Icc ((coordinateBox S R hR).face i), facePullback ω i 0 x (standardBasis n) := by
  rw [coordinateBox_face]
  apply integral_orthant_eq_box (faceIndices S i) R hR
  exact face_density_support_bound ω R hbound i 0

theorem continuous_extDeriv_density {n : ℕ} (ω : Form n) (hω : ContDiff ℝ 1 ω) :
    Continuous (fun x ↦ extDeriv ω x (standardBasis (n + 1))) :=
  (ContinuousAlternatingMap.apply ℝ _ ℝ (standardBasis (n + 1))).continuous.comp
    ((ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ _ ℝ).continuous.comp
      (hω.continuous_fderiv (by decide)))

theorem continuous_face_density {n : ℕ} (ω : Form n) (hω : Continuous ω)
    (i : Fin (n + 1)) (c : ℝ) :
    Continuous (fun x ↦ facePullback ω i c x (standardBasis n)) := by
  simp only [facePullback_standardBasis, faceCoefficient]
  exact (ContinuousAlternatingMap.apply ℝ _ ℝ (i.removeNth (standardBasis (n + 1)))).continuous.comp
    (hω.comp (continuous_const.finInsertNth i continuous_id))

/-- Stokes on the orthant, derived from a single finite box enclosing both supports. -/
theorem integral_extDeriv_eq_lower_faces_of_support_bound {n : ℕ}
    (ω : Form n) (S : Finset (Fin (n + 1))) (hω : ContDiff ℝ 1 ω)
    (R : ℝ) (hR : 0 < R)
    (hbound : ∀ x ∈ Function.support ω, ∀ i, |x i| < R)
    (hD : ∀ x ∈ Function.support (fun y ↦ extDeriv ω y (standardBasis (n + 1))), ∀ i, |x i| < R) :
    (∫ x in orthant S, extDeriv ω x (standardBasis (n + 1))) =
      ∑ i ∈ S, -((-1 : ℝ) ^ i.val) •
        ∫ x in orthant (faceIndices S i), facePullback ω i 0 x (standardBasis n) := by
  rw [integral_orthant_eq_box S R hR _ hD,
    BoxStokes.integral_Icc_extDeriv_eq_faces _ ω (fun x hx ↦ hω.contDiffAt)]
  have hu (i : Fin (n + 1)) :
      (∫ x in Box.Icc ((coordinateBox S R hR).face i),
        facePullback ω i ((coordinateBox S R hR).upper i) x (standardBasis n)) = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro x hx
    exact face_density_eq_zero_of_abs_ge ω R hbound i R (le_abs_self R) x
  simp only [hu, zero_sub, smul_neg]
  rw [← Finset.sum_subset (Finset.subset_univ S)]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [coordinateBox_lower, if_pos hi, ← integral_lower_face_eq_box ω S R hR hbound i]
    simp only [neg_smul]
  · intro i hi hni
    rw [coordinateBox_lower, if_neg hni]
    have hz : (∫ x in Box.Icc ((coordinateBox S R hR).face i),
        facePullback ω i (-R) x (standardBasis n)) = 0 := by
      apply setIntegral_eq_zero_of_forall_eq_zero
      intro x hx
      exact face_density_eq_zero_of_abs_ge ω R hbound i (-R) (by simpa using le_abs_self R) x
    rw [hz, smul_zero, neg_zero]


/-- Stokes for a genuinely compactly supported C1 form on an arbitrary coordinate
orthant. Only the lower faces indexed by S occur, with the signs -(-1)^i. -/
theorem integral_extDeriv_eq_lower_faces {n : ℕ} (ω : Form n)
    (S : Finset (Fin (n + 1))) (hω : ContDiff ℝ 1 ω) (hcompact : HasCompactSupport ω) :
    (∫ x in orthant S, extDeriv ω x (standardBasis (n + 1))) =
      ∑ i ∈ S, -((-1 : ℝ) ^ i.val) •
        ∫ x in orthant (faceIndices S i), facePullback ω i 0 x (standardBasis n) := by
  obtain ⟨R, hR, hbound⟩ := CompactSupportBoxes.exists_pos_tsupport_bound ω hcompact
  apply integral_extDeriv_eq_lower_faces_of_support_bound ω S hω R hR
  · intro x hx
    exact hbound x (subset_tsupport ω hx)
  · intro x hx
    exact hbound x (CompactSupportBoxes.support_extDeriv_density_subset ω hx)

/-- The body integral is genuinely Lebesgue integrable, including on unbounded orthants. -/
theorem integrableOn_orthant_extDeriv {n : ℕ} (ω : Form n)
    (S : Finset (Fin (n + 1))) (hω : ContDiff ℝ 1 ω) (hcompact : HasCompactSupport ω) :
    IntegrableOn (fun x ↦ extDeriv ω x (standardBasis (n + 1))) (orthant S) :=
  (CompactSupportBoxes.integrable_extDeriv_density ω hω hcompact).integrableOn

/-- All actual lower-face pullback integrals are finite, including zero-dimensional faces. -/
theorem integrableOn_lower_face {n : ℕ} (ω : Form n)
    (S : Finset (Fin (n + 1))) (hω : Continuous ω) (hcompact : HasCompactSupport ω)
    (i : Fin (n + 1)) :
    IntegrableOn (fun x ↦ facePullback ω i 0 x (standardBasis n)) (orthant (faceIndices S i)) := by
  obtain ⟨R, hR, hbound⟩ := CompactSupportBoxes.exists_pos_tsupport_bound ω hcompact
  apply integrableOn_orthant_of_support_bound (faceIndices S i) R hR _
    (continuous_face_density ω hω i 0)
  exact face_density_support_bound ω R (fun x hx ↦ hbound x (subset_tsupport ω hx)) i 0

/-- The empty corner set gives the whole-space vanishing theorem. -/
theorem integral_whole_extDeriv_eq_zero {n : ℕ} (ω : Form n)
    (hω : ContDiff ℝ 1 ω) (hcompact : HasCompactSupport ω) :
    (∫ x, extDeriv ω x (standardBasis (n + 1))) = 0 := by
  simpa only [orthant_empty, MeasureTheory.setIntegral_univ, Finset.sum_empty] using
    integral_extDeriv_eq_lower_faces ω ∅ hω hcompact

/-- For a closed compactly supported form the actual oriented orthant boundary integral vanishes. -/
theorem lower_boundary_eq_zero_of_closed {n : ℕ} (ω : Form n)
    (S : Finset (Fin (n + 1))) (hω : ContDiff ℝ 1 ω) (hcompact : HasCompactSupport ω)
    (hclosed : ∀ x ∈ orthant S, extDeriv ω x = 0) :
    (∑ i ∈ S, -((-1 : ℝ) ^ i.val) •
      ∫ x in orthant (faceIndices S i), facePullback ω i 0 x (standardBasis n)) = 0 := by
  rw [← integral_extDeriv_eq_lower_faces ω S hω hcompact]
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro x hx
  rw [hclosed x hx]
  rfl

end EnvelopingIsomorphism.Deformation.Kontsevich.CompactOrthantStokes
