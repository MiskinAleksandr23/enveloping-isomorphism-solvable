import EnvelopingIsomorphism.Deformation.Kontsevich.NormalCrossingCylinderCoordinates
import EnvelopingIsomorphism.Deformation.Kontsevich.LogMonomialPrimitiveIntegrability

/-! A compactly cut off actual logarithmic monomial primitive defines a local
normal-crossing current with zero integrated exterior derivative. All regularity,
integrability, support, and shrinking-flux facts are derived from local data. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Kontsevich.CompactMonomialStokes

open Set MeasureTheory ContinuousAlternatingMap Filter
open BoxStokes NormalCrossingStokes
open scoped Topology

def polydisc (N : ℕ) (ρ : ℝ) : Set (Space N) := {z | ∀ i, ‖z i‖ < ρ}

/-- Only actual local unit/cutoff hypotheses are bundled here. There is no
regularity, L¹, boundary, or Stokes hypothesis for the resulting current. -/
structure LocalData (N : ℕ) where
  a : Fin (Dim N) → Fin (N + 1) → ℤ
  u : Fin (Dim N) → Space N → ℂ
  χ : Space N → ℝ
  ρ : ℝ
  D : ℝ
  c : ℝ
  M : ℝ
  ρ_pos : 0 < ρ
  c_pos : 0 < c
  U : Set (Space N)
  open_U : IsOpen U
  cutoff_C1 : ContDiff ℝ 1 χ
  cutoff_compact : HasCompactSupport χ
  support_U : tsupport χ ⊆ U
  support_polydisc : tsupport χ ⊆ polydisc N ρ
  units_C2 : ∀ j, ContDiffOn ℝ 2 (u j) U
  unit_lower : ∀ z ∈ U ∩ polydisc N ρ, ∀ j, c ≤ ‖u j z‖
  unit_derivative : ∀ z ∈ U ∩ polydisc N ρ, ∀ j, ‖fderiv ℝ (u j) z‖ ≤ D
  first_unit_upper : ∀ z ∈ U ∩ polydisc N ρ, ‖u 0 z‖ ≤ M

def beta {N : ℕ} (d : LocalData N) : CrossingForm N :=
  LogRadialPrimitive.primitive (LogMonomial.coordinateMonomial d.a d.u)

def current {N : ℕ} (d : LocalData N) : CrossingForm N := fun z ↦ d.χ z • beta d z

theorem hasCompactSupport_current {N : ℕ} (d : LocalData N) : HasCompactSupport (current d) :=
  d.cutoff_compact.smul_right

theorem tsupport_current_subset {N : ℕ} (d : LocalData N) : tsupport (current d) ⊆ tsupport d.χ :=
  tsupport_smul_subset_left d.χ (beta d)

theorem contDiffAt_primitive_of_C2 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} (f : Fin (n + 1) → E → ℂ) {x : E}
    (hf : ∀ j, ContDiffAt ℝ 2 (f j) x) (hne : ∀ j, f j x ≠ 0) :
    ContDiffAt ℝ 1 (LogRadialPrimitive.primitive f) x := by
  have hlog : ContDiffAt ℝ 2 (LogRadialPrimitive.logarithms f) x := by
    apply contDiffAt_pi.mpr
    intro j
    exact ((hf j).norm ℂ (hne j)).log (norm_ne_zero_iff.mpr (hne j))
  have hD : ContDiffAt ℝ 1 (fderiv ℝ (LogRadialPrimitive.logarithms f)) x :=
    hlog.fderiv_right (by norm_num)
  have hP := ((contDiff_compContinuousLinearMap
    ((coordinateVolume n).compContinuousLinearMap (LogRadialPrimitive.tailProjection n))).of_le
      (show (1 : WithTop ℕ∞) ≤ ⊤ by simp)).contDiffAt.comp x hD
  have hfirst : ContDiffAt ℝ 1 (fun y ↦ LogRadialPrimitive.logarithms f y 0) x :=
    (contDiff_apply ℝ ℝ (0 : Fin (n + 1))).contDiffAt.comp x (hlog.of_le (by norm_num))
  convert hfirst.smul hP using 1
  funext y
  ext v
  rfl

theorem contDiffAt_beta {N : ℕ} (d : LocalData N) {z : Space N}
    (hz : z ∈ d.U ∩ polydisc N d.ρ) (hreg : z ∈ regularLocus N) : ContDiffAt ℝ 1 (beta d) z := by
  apply contDiffAt_primitive_of_C2
  · intro j
    exact LogMonomial.contDiffAt_coordinateMonomial d.a d.u j z
      ((d.units_C2 j).contDiffAt (d.open_U.mem_nhds hz.1)) hreg
  · intro j
    exact LogMonomial.value_ne_zero (d.a j)
      (norm_pos_iff.mp (d.c_pos.trans_le (d.unit_lower z hz j))) hreg

theorem contDiffOn_current {N : ℕ} (d : LocalData N) : ContDiffOn ℝ 1 (current d) (regularLocus N) := by
  intro z hreg
  by_cases hz : z ∈ tsupport d.χ
  · exact (d.cutoff_C1.contDiffAt.smul
      (contDiffAt_beta d ⟨d.support_U hz, d.support_polydisc hz⟩ hreg)).contDiffWithinAt
  · apply ContDiffAt.contDiffWithinAt
    apply (contDiffAt_const (c := (0 : Space N [⋀^Fin (Degree N)]→L[ℝ] ℝ))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hz] with y hy
    simp only [current, hy, Pi.zero_apply, zero_smul]

theorem norm_frame_le_one (N : ℕ) (j : Fin (Dim N)) : ‖frame N j‖ ≤ 1 := by
  refine Fin.addCases (m := N + 1) (n := N + 1) (fun i ↦ ?_) (fun i ↦ ?_) j
  · change ‖frame N (radiusIndex i)‖ ≤ 1
    rw [frame_radius]
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro k
    by_cases h : k = i <;> simp [h]
  · change ‖frame N (angleIndex i)‖ ≤ 1
    rw [frame_angle]
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro k
    by_cases h : k = i <;> simp [h]

theorem exists_cutoff_bounds {N : ℕ} (d : LocalData N) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ (∀ z, ‖d.χ z‖ ≤ A) ∧ (∀ z, ‖fderiv ℝ d.χ z‖ ≤ B) := by
  obtain ⟨A, hA⟩ := d.cutoff_C1.continuous.bounded_above_of_compact_support d.cutoff_compact
  obtain ⟨B, hB⟩ := (d.cutoff_C1.continuous_fderiv (by norm_num)).bounded_above_of_compact_support
    (d.cutoff_compact.fderiv (𝕜 := ℝ))
  exact ⟨max 0 A, max 0 B, le_max_left _ _, le_max_left _ _,
    fun z ↦ (hA z).trans (le_max_right _ _), fun z ↦ (hB z).trans (le_max_right _ _)⟩

def cutoffTerm {N : ℕ} (d : LocalData N) (z : Space N) : Space N [⋀^Fin (Dim N)]→L[ℝ] ℝ :=
  alternatizeUncurryFin ((fderiv ℝ d.χ z).smulRight (beta d z))

theorem extDeriv_current {N : ℕ} (d : LocalData N) {z : Space N}
    (hz : z ∈ tsupport d.χ) (hreg : z ∈ regularLocus N) :
    extDeriv (current d) z = d.χ z • extDeriv (beta d) z + cutoffTerm d z := by
  change extDeriv (fun y ↦ d.χ y • beta d y) z = _
  rw [extDeriv, fderiv_fun_smul (d.cutoff_C1.differentiable (by norm_num) z)
    ((contDiffAt_beta d ⟨d.support_U hz, d.support_polydisc hz⟩ hreg).differentiableAt (by norm_num)),
    alternatizeUncurryFin_add, alternatizeUncurryFin_smul]
  rfl

theorem cutoffTerm_apply {N : ℕ} (d : LocalData N) (z : Space N) :
    cutoffTerm d z (frame N) = ∑ j : Fin (Dim N), (-1 : ℝ) ^ j.val •
      (fderiv ℝ d.χ z (frame N j) • beta d z (j.removeNth (frame N))) := by
  simp [cutoffTerm, alternatizeUncurryFin_apply]

def betaBound {N : ℕ} (d : LocalData N) : ℝ :=
  LogMonomial.primitiveIntegrabilityBound d.a d.D d.c d.M
def derivativeBound {N : ℕ} (d : LocalData N) : ℝ := LogMonomial.uniformDeterminantBound d.a d.D d.c

theorem betaBound_nonneg {N : ℕ} (d : LocalData N) : 0 ≤ betaBound d := by
  unfold betaBound LogMonomial.primitiveIntegrabilityBound
  apply mul_nonneg
  · exact LogMonomial.logarithmBound_nonneg _ ((abs_nonneg _).trans (le_max_left _ _))
  · unfold LogMonomial.uniformDeterminantBound LogMonomial.exponentBound
    positivity

theorem derivativeBound_nonneg {N : ℕ} (d : LocalData N) : 0 ≤ derivativeBound d := by
  unfold derivativeBound LogMonomial.uniformDeterminantBound LogMonomial.exponentBound
  positivity

theorem norm_beta_coefficient_le {N : ℕ} (d : LocalData N) {z : Space N}
    (hz : z ∈ d.U ∩ polydisc N d.ρ) (hreg : z ∈ regularLocus N)
    (v : Fin (Degree N) → Space N) (hv : ∀ j, ‖v j‖ ≤ 1) :
    ‖beta d z v‖ ≤ betaBound d * NormalCrossing.majorant (fun _ : Fin (N + 1) ↦ 1) z :=
  LogMonomial.norm_primitiveCoefficient_le_majorant d.a d.u v z
    (fun j ↦ ((d.units_C2 j).contDiffAt (d.open_U.mem_nhds hz.1)).differentiableAt (by norm_num)) hreg
    d.D d.c d.M d.c_pos (fun j ↦ d.unit_derivative z hz j.succ) (d.unit_lower z hz)
    (d.first_unit_upper z hz) hv

theorem norm_extDeriv_beta_coefficient_le {N : ℕ} (d : LocalData N) {z : Space N}
    (hz : z ∈ d.U ∩ polydisc N d.ρ) (hreg : z ∈ regularLocus N)
    (v : Fin (Dim N) → Space N) (hv : ∀ j, ‖v j‖ ≤ 1) :
    ‖extDeriv (beta d) z v‖ ≤ derivativeBound d * NormalCrossing.majorant (fun _ : Fin (N + 1) ↦ 0) z := by
  have hu (j : Fin (Dim N)) : ContDiffAt ℝ 2 (d.u j) z :=
    (d.units_C2 j).contDiffAt (d.open_U.mem_nhds hz.1)
  have hu0 (j : Fin (Dim N)) : d.u j z ≠ 0 := norm_pos_iff.mp (d.c_pos.trans_le (d.unit_lower z hz j))
  rw [beta, LogMonomial.extDeriv_primitive_eq_actualDeterminant_of_C2 d.a d.u v z hu hu0 hreg,
    Real.norm_eq_abs]
  have h := (LogMonomial.abs_actualRadialMatrix_det_le d.a d.u v
    (fun j ↦ (hu j).differentiableAt (by norm_num)) hu0 hreg).trans
      (mul_le_mul_of_nonneg_right
        (LogMonomial.coefficientBound_le_unitBounds d.a d.u v z d.D d.c d.c_pos
          (d.unit_derivative z hz) (d.unit_lower z hz) hv)
        (Finset.prod_nonneg (fun _ _ ↦ by positivity)))
  simpa only [derivativeBound, NormalCrossing.majorant, NormalCrossing.factor, pow_zero, mul_one] using h

theorem punctured_mem_regular {N : ℕ} {ρ : ℝ} {z : Space N}
    (hz : z ∈ NormalCrossing.puncturedPolydisc (fun _ : Fin (N + 1) ↦ ρ)) : z ∈ regularLocus N :=
  fun j ↦ norm_pos_iff.mp (hz j trivial).1

theorem punctured_mem_polydisc {N : ℕ} {ρ : ℝ} {z : Space N}
    (hz : z ∈ NormalCrossing.puncturedPolydisc (fun _ : Fin (N + 1) ↦ ρ)) : z ∈ polydisc N ρ :=
  fun j ↦ (hz j trivial).2

theorem integrableOn_beta_coefficient {N : ℕ} (d : LocalData N)
    (v : Fin (Degree N) → Space N) (hv : ∀ j, ‖v j‖ ≤ 1) :
    IntegrableOn (fun z ↦ beta d z v)
      (d.U ∩ NormalCrossing.puncturedPolydisc (fun _ : Fin (N + 1) ↦ d.ρ)) := by
  have hc : ContinuousOn (fun z ↦ beta d z v)
      (d.U ∩ NormalCrossing.puncturedPolydisc (fun _ : Fin (N + 1) ↦ d.ρ)) := by
    intro z hz
    exact ((ContinuousAlternatingMap.apply ℝ _ ℝ v).continuous.continuousAt.comp
      (contDiffAt_beta d ⟨hz.1, punctured_mem_polydisc hz.2⟩ (punctured_mem_regular hz.2)).continuousAt).continuousWithinAt
  have hm0 : IntegrableOn (fun z ↦ betaBound d * NormalCrossing.majorant (fun _ : Fin (N + 1) ↦ 1) z)
      (NormalCrossing.puncturedPolydisc (fun _ : Fin (N + 1) ↦ d.ρ)) :=
    (NormalCrossing.integrableOn_majorant (fun _ : Fin (N + 1) ↦ 1) (fun _ ↦ d.ρ)).const_mul (betaBound d)
  have hm := hm0.mono_set (inter_subset_right (s := d.U))
  apply hm.mono' (hc.aestronglyMeasurable (d.open_U.measurableSet.inter (NormalCrossing.measurableSet_puncturedPolydisc _)))
  filter_upwards [ae_restrict_mem (d.open_U.measurableSet.inter (NormalCrossing.measurableSet_puncturedPolydisc _))] with z hz
  exact norm_beta_coefficient_le d ⟨hz.1, punctured_mem_polydisc hz.2⟩ (punctured_mem_regular hz.2) v hv

theorem norm_current_density_le {N : ℕ} (d : LocalData N) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hχ : ∀ z, ‖d.χ z‖ ≤ A) (hDχ : ∀ z, ‖fderiv ℝ d.χ z‖ ≤ B)
    (z : Space N) (hreg : z ∈ regularLocus N) :
    ‖density (current d) z‖ ≤
      A * derivativeBound d * NormalCrossing.majorant (fun _ : Fin (N + 1) ↦ 0) z +
        (Dim N : ℝ) * B * betaBound d * NormalCrossing.majorant (fun _ : Fin (N + 1) ↦ 1) z := by
  have h0 := NormalCrossing.majorant_nonneg (fun _ : Fin (N + 1) ↦ 0) z
  have h1 := NormalCrossing.majorant_nonneg (fun _ : Fin (N + 1) ↦ 1) z
  have hβ := betaBound_nonneg d
  have hβD := derivativeBound_nonneg d
  by_cases hz : z ∈ tsupport d.χ
  · have hloc := And.intro (d.support_U hz) (d.support_polydisc hz)
    have happly (j : Fin (Dim N)) : ‖fderiv ℝ d.χ z (frame N j)‖ ≤ B := by
      calc
        _ ≤ ‖fderiv ℝ d.χ z‖ * ‖frame N j‖ := (fderiv ℝ d.χ z).le_opNorm _
        _ ≤ B * 1 := mul_le_mul (hDχ z) (norm_frame_le_one N j) (norm_nonneg _) hB
        _ = B := mul_one B
    rw [density, extDeriv_current d hz hreg, ContinuousAlternatingMap.add_apply,
      ContinuousAlternatingMap.smul_apply, cutoffTerm_apply]
    calc
      _ ≤ ‖d.χ z‖ * ‖extDeriv (beta d) z (frame N)‖ +
          ∑ j : Fin (Dim N), ‖(-1 : ℝ) ^ j.val •
            (fderiv ℝ d.χ z (frame N j) • beta d z (j.removeNth (frame N)))‖ := by
        exact (norm_add_le _ _).trans (add_le_add (le_of_eq (norm_smul _ _)) (norm_sum_le _ _))
      _ ≤ A * (derivativeBound d * NormalCrossing.majorant (fun _ : Fin (N + 1) ↦ 0) z) +
          ∑ _j : Fin (Dim N), B * (betaBound d * NormalCrossing.majorant (fun _ : Fin (N + 1) ↦ 1) z) := by
        apply add_le_add
        · exact mul_le_mul (hχ z) (norm_extDeriv_beta_coefficient_le d hloc hreg (frame N) (norm_frame_le_one N))
            (norm_nonneg _) hA
        · apply Finset.sum_le_sum
          intro j hj
          simp only [norm_smul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
          exact mul_le_mul (happly j)
            (norm_beta_coefficient_le d hloc hreg _ (fun k ↦ norm_frame_le_one N (j.succAbove k)))
            (norm_nonneg _) hB
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  · have hzω : z ∉ tsupport (current d) := fun h ↦ hz (tsupport_current_subset d h)
    rw [density, CompactSupportBoxes.extDeriv_zero_of_notMem_tsupport _ hzω]
    change ‖(0 : ℝ)‖ ≤ _
    rw [norm_zero]
    positivity

theorem integrable_current_density {N : ℕ} (d : LocalData N) : Integrable (density (current d)) := by
  obtain ⟨A, B, hA, hB, hχ, hDχ⟩ := exists_cutoff_bounds d
  let P := NormalCrossing.puncturedPolydisc (fun _ : Fin (N + 1) ↦ d.ρ)
  have hP : MeasurableSet P := NormalCrossing.measurableSet_puncturedPolydisc _
  have hc : ContinuousOn (density (current d)) P := by
    intro z hz
    exact (NormalCrossingStokes.continuousAt_density (current d) z
      ((contDiffOn_current d).contDiffAt ((isOpen_regularLocus N).mem_nhds (punctured_mem_regular hz)))).continuousWithinAt
  have hm := ((NormalCrossing.integrableOn_majorant (fun _ : Fin (N + 1) ↦ 0) (fun _ ↦ d.ρ)).const_mul
    (A * derivativeBound d)).add
      ((NormalCrossing.integrableOn_majorant (fun _ : Fin (N + 1) ↦ 1) (fun _ ↦ d.ρ)).const_mul
        ((Dim N : ℝ) * B * betaBound d))
  have hi : IntegrableOn (density (current d)) P := by
    apply hm.mono' (hc.aestronglyMeasurable hP)
    filter_upwards [ae_restrict_mem hP] with z hz
    exact norm_current_density_le d A B hA hB hχ hDχ z (punctured_mem_regular hz)
  have ha : density (current d) =ᵐ[volume] P.indicator (density (current d)) := by
    filter_upwards [ae_mem_regularLocus N] with z hz
    by_cases hp : z ∈ P
    · rw [indicator_of_mem hp]
    · rw [indicator_of_notMem hp]
      by_contra hn
      have hs := CompactSupportBoxes.support_extDeriv_apply_subset (current d) (frame N) hn
      have hχs := tsupport_current_subset d hs
      exact hp (fun j hj ↦ ⟨norm_pos_iff.mpr (hz j), d.support_polydisc hχs j⟩)
  exact (integrable_congr ha).mpr ((integrable_indicator_iff hP).mpr hi)

open NormalCrossingCylinderCoordinates

theorem contDiff_nativeCylinder {N : ℕ} (i : Fin (N + 1)) (r : ℝ) :
    ContDiff ℝ ⊤ (nativeCylinder i r) := by
  apply contDiff_pi.mpr
  intro k
  induction k using i.succAboveCases with
  | x =>
    have h : ContDiff ℝ ⊤ (fun p : MixedComplex N ↦ (r : ℂ) * circleParameter p.1) :=
      contDiff_const.mul (contDiff_circleParameter.comp contDiff_fst)
    simpa only [nativeCylinder, Fin.insertNth_apply_same, LogCircle.shrinkingCircle] using h
  | p k =>
    simp only [nativeCylinder, Fin.insertNth_apply_succAbove]
    convert (((ContinuousLinearMap.proj k : (Fin N → ℂ) →L[ℝ] ℂ).comp
      (ContinuousLinearMap.snd ℝ ℝ (Fin N → ℂ))).contDiff) using 1
    rfl

theorem nativeCylinder_regular {N : ℕ} (i : Fin (N + 1)) {r : ℝ} (hr : 0 < r)
    (p : MixedComplex N) (hp : ∀ k, p.2 k ≠ 0) : nativeCylinder i r p ∈ regularLocus N := by
  intro k
  induction k using i.succAboveCases with
  | x =>
    simp only [nativeCylinder, Fin.insertNth_apply_same]
    apply norm_pos_iff.mp
    simpa only [LogCircle.norm_shrinkingCircle, abs_of_pos hr] using hr
  | p k => simpa only [nativeCylinder, Fin.insertNth_apply_succAbove] using hp k

theorem continuousAt_nativeDensity_current {N : ℕ} (d : LocalData N) (i : Fin (N + 1))
    {r : ℝ} (hr : 0 < r) (p : MixedComplex N) (hp : ∀ k, p.2 k ≠ 0) :
    ContinuousAt (nativeDensity (current d) i r) p := by
  have hc := (contDiffOn_current d).contDiffAt
    ((isOpen_regularLocus N).mem_nhds (nativeCylinder_regular i hr p hp))
  have hD : ContDiffAt ℝ 1 (fderiv ℝ (nativeCylinder i r)) p :=
    (contDiff_nativeCylinder i r).contDiffAt.fderiv_right (by simp)
  have hpb := DifferentiableAt.continuousAlternatingMapCompContinuousLinearMap
    ((hc.differentiableAt (by norm_num)).comp p (hasFDerivAt_nativeCylinder i r p).differentiableAt)
    (hD.differentiableAt (by norm_num))
  exact (ContinuousAlternatingMap.apply ℝ _ ℝ (mixedFrame i)).continuous.continuousAt.comp hpb.continuousAt

theorem prod_erase_eq_remaining {N : ℕ} (f : Fin (N + 1) → ℝ) (i : Fin (N + 1)) (hi : f i ≠ 0) :
    (∏ k ∈ Finset.univ.erase i, f k) = ∏ k : Fin N, f (i.succAbove k) := by
  apply mul_left_cancel₀ hi
  exact (Finset.mul_prod_erase Finset.univ f (Finset.mem_univ i)).trans (Fin.prod_univ_succAbove f i)

theorem boundary_coefficient_bound {N : ℕ} (d : LocalData N) {x : Space N}
    (hx : x ∈ d.U ∩ polydisc N d.ρ) (i : Fin (N + 1)) (r : ℝ) (hr : 0 ≤ r)
    (hr1 : r ≤ 1) (p : MixedComplex N) :
    RadialPoleDeterminant.coefficientBound
      ((LogMonomial.smoothRows (fun j : Fin (Degree N) ↦ d.u j.succ) (tangentFrame i r p) x).updateCol
        (angularSlot i) (LogMonomial.angularUnitColumn (fun j : Fin (Degree N) ↦ d.u j.succ) i p.1 x))
      (LogMonomial.unitRadialRows (tangentFrame i r p) x)
      (LogMonomial.integerCoefficients (fun j : Fin (Degree N) ↦ d.a j.succ)) ≤
      LogMonomial.uniformDeterminantBound (fun j : Fin (Degree N) ↦ d.a j.succ) d.D d.c := by
  apply RadialPoleDeterminant.coefficientBound_le_uniform _ _ _
    (max 1 (d.D / d.c)) (LogMonomial.exponentBound (fun j : Fin (Degree N) ↦ d.a j.succ))
    (le_max_left _ _) (LogMonomial.one_le_exponentBound _)
  · intro j k
    by_cases hk : k = angularSlot i
    · subst k
      simp only [Matrix.updateCol_self]
      exact (LogMonomial.smoothRows_bound (fun j : Fin (Degree N) ↦ d.u j.succ)
        (fun _ ↦ LogMonomial.unitAngularTangent i p.1) x d.D d.c d.c_pos
        (fun j ↦ d.unit_derivative x hx j.succ) (fun j ↦ d.unit_lower x hx j.succ)
        (fun _ ↦ LogMonomial.norm_unitAngularTangent_le i p.1) j (angularSlot i)).trans (le_max_right _ _)
    · rw [Matrix.updateCol_apply, if_neg hk]
      exact (LogMonomial.smoothRows_bound (fun j : Fin (Degree N) ↦ d.u j.succ)
        (tangentFrame i r p) x d.D d.c d.c_pos
        (fun j ↦ d.unit_derivative x hx j.succ) (fun j ↦ d.unit_lower x hx j.succ)
        (fun k ↦ norm_tangentFrame_le_one i r hr hr1 p k) j k).trans (le_max_right _ _)
  · intro ν j
    exact (LogMonomial.unitRadialRows_bound_one (tangentFrame i r p)
      (fun k ↦ norm_tangentFrame_le_one i r hr hr1 p k) x ν j).trans (le_max_left _ _)
  · exact LogMonomial.integerCoefficients_bound _

/-- The genuine monomial primitive bound on the actual circle face, at arbitrary
real angle. No angular-interval hypothesis or supplied tangent bound is used. -/
theorem norm_beta_nativeFrame_le {N : ℕ} (d : LocalData N) (i : Fin (N + 1))
    (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) (p : MixedComplex N)
    (hp : ∀ k, p.2 k ≠ 0) (hx : nativeCylinder i r p ∈ d.U ∩ polydisc N d.ρ) :
    ‖beta d (nativeCylinder i r p) (tangentFrame i r p)‖ ≤
      betaBound d * r * (1 + |Real.log r|) * NormalCrossing.boundaryMajorant (fun _ : Fin N ↦ 1) p := by
  let x := nativeCylinder i r p
  have hu (j : Fin (Dim N)) : DifferentiableAt ℝ (d.u j) x :=
    ((d.units_C2 j).contDiffAt (d.open_U.mem_nhds hx.1)).differentiableAt (by norm_num)
  have hu0 (j : Fin (Dim N)) : d.u j x ≠ 0 := norm_pos_iff.mp (d.c_pos.trans_le (d.unit_lower x hx j))
  have hreg := nativeCylinder_regular i hr p hp
  have hlog := LogMonomial.abs_log_norm_value_le (d.a 0) (hu0 0) hreg _
    (LogMonomial.abs_log_norm_le_of_unitBounds d.c_pos (d.unit_lower x hx 0) (d.first_unit_upper x hx))
  rw [Fin.prod_univ_succAbove _ i] at hlog
  simp only [x, nativeCylinder, Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove,
    LogCircle.norm_shrinkingCircle, abs_of_pos hr] at hlog
  have hd := LogMonomial.abs_actualRadialMatrix_boundary_le
    (fun j : Fin (Degree N) ↦ d.a j.succ) (fun j ↦ d.u j.succ) (tangentFrame i r p) x
    (angularSlot i) i r p.1 hr.le (by simp [x, nativeCylinder, LogCircle.shrinkingCircle])
    (tangentFrame_angularSlot i r p) (fun j hj ↦ tangentFrame_distinguished i r p j hj)
    (fun j ↦ hu j.succ) (fun j ↦ hu0 j.succ) hreg
  rw [prod_erase_eq_remaining _ i (by positivity)] at hd
  simp only [x, nativeCylinder, Fin.insertNth_apply_succAbove] at hd
  have hd' := hd.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (boundary_coefficient_bound d hx i r hr.le hr1 p) hr.le)
    (Finset.prod_nonneg (fun _ _ ↦ by positivity)))
  have hK := LogMonomial.logarithmBound_nonneg (d.a 0)
    (L := max |Real.log d.c| |Real.log d.M|) ((abs_nonneg _).trans (le_max_left _ _))
  rw [beta, LogMonomial.primitive_eq_log_mul_actualDeterminant d.a d.u _ x hu hu0 hreg,
    norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  refine (mul_le_mul hlog hd' (abs_nonneg _) (by positivity)).trans_eq ?_
  simp only [betaBound, LogMonomial.primitiveIntegrabilityBound, NormalCrossing.boundaryMajorant,
    NormalCrossing.majorant_eq_prod_mul, pow_one]
  ring

theorem norm_nativeDensity_current_le {N : ℕ} (d : LocalData N) (A : ℝ) (hA : 0 ≤ A)
    (hχ : ∀ z, ‖d.χ z‖ ≤ A) (i : Fin (N + 1)) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (p : MixedComplex N) (hp : ∀ k, p.2 k ≠ 0) :
    ‖nativeDensity (current d) i r p‖ ≤
      A * betaBound d * r * (1 + |Real.log r|) * NormalCrossing.boundaryMajorant (fun _ : Fin N ↦ 1) p := by
  rw [nativeDensity_eq_tangentFrame]
  change ‖d.χ (nativeCylinder i r p) • beta d (nativeCylinder i r p) (tangentFrame i r p)‖ ≤ _
  rw [norm_smul]
  by_cases hz : d.χ (nativeCylinder i r p) = 0
  · rw [hz, norm_zero, zero_mul]
    have hb := betaBound_nonneg d
    have hm := NormalCrossing.majorant_nonneg (fun _ : Fin N ↦ 1) p.2
    change (0 : ℝ) ≤ _
    positivity
  · have hs := subset_tsupport d.χ hz
    have hb := norm_beta_nativeFrame_le d i r hr hr1 p hp ⟨d.support_U hs, d.support_polydisc hs⟩
    exact (mul_le_mul (hχ _) hb (norm_nonneg _) hA).trans_eq (by ring)

def centeredRegion {N : ℕ} (d : LocalData N) : Set (MixedComplex N) :=
  Icc (-Real.pi) Real.pi ×ˢ NormalCrossing.puncturedPolydisc (fun _ : Fin N ↦ d.ρ)

theorem measurableSet_centeredRegion {N : ℕ} (d : LocalData N) : MeasurableSet (centeredRegion d) :=
  measurableSet_Icc.prod (NormalCrossing.measurableSet_puncturedPolydisc _)

theorem integrableOn_centeredMajorant {N : ℕ} (d : LocalData N) :
    IntegrableOn (NormalCrossing.boundaryMajorant (fun _ : Fin N ↦ 1)) (centeredRegion d) := by
  have hθ : IntegrableOn (fun _ : ℝ ↦ (1 : ℝ)) (Icc (-Real.pi) Real.pi) :=
    continuous_const.continuousOn.integrableOn_compact isCompact_Icc
  change Integrable (fun p : MixedComplex N ↦ NormalCrossing.majorant (fun _ : Fin N ↦ 1) p.2)
    (volume.restrict (Icc (-Real.pi) Real.pi ×ˢ NormalCrossing.puncturedPolydisc (fun _ : Fin N ↦ d.ρ)))
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
  simpa only [one_mul] using hθ.mul_prod (NormalCrossing.integrableOn_majorant (fun _ : Fin N ↦ 1) (fun _ ↦ d.ρ))

theorem continuousOn_nativeDensity_current {N : ℕ} (d : LocalData N) (i : Fin (N + 1))
    {r : ℝ} (hr : 0 < r) : ContinuousOn (nativeDensity (current d) i r) (centeredRegion d) := by
  intro p hp
  exact (continuousAt_nativeDensity_current d i hr p
    (fun k ↦ norm_pos_iff.mp (hp.2 k trivial).1)).continuousWithinAt

theorem nativeDensity_zero_outside_centered {N : ℕ} (d : LocalData N) (i : Fin (N + 1))
    (r : ℝ) (hr : 0 < r) (p : MixedComplex N) (hp : p ∈ nativeRegion N r)
    (hn : p ∉ centeredRegion d) : nativeDensity (current d) i r p = 0 := by
  have hz : d.χ (nativeCylinder i r p) = 0 := by
    by_contra hχ
    have hs := d.support_polydisc (subset_tsupport d.χ hχ)
    apply hn
    refine ⟨hp.1, fun k hk ↦ ⟨hr.trans_le (hp.2 k hk), ?_⟩⟩
    simpa only [nativeCylinder, Fin.insertNth_apply_succAbove] using hs (i.succAbove k)
  rw [nativeDensity_eq_tangentFrame]
  change (d.χ (nativeCylinder i r p) • beta d (nativeCylinder i r p)) _ = 0
  rw [hz, zero_smul]
  rfl

theorem nativeIntegral_eq_centeredIndicator {N : ℕ} (d : LocalData N) (i : Fin (N + 1))
    (r : ℝ) (hr : 0 < r) :
    (∫ p in nativeRegion N r, nativeDensity (current d) i r p) =
      ∫ p in centeredRegion d, (nativeRegion N r).indicator (nativeDensity (current d) i r) p := by
  rw [setIntegral_indicator (measurableSet_nativeRegion N r), inter_comm]
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (measurableSet_nativeRegion N r) inter_subset_left
  rintro p ⟨hp, hn⟩
  exact nativeDensity_zero_outside_centered d i r hr p hp (fun hc ↦ hn ⟨hp, hc⟩)

theorem nativeIntegral_bound {N : ℕ} (d : LocalData N) (A : ℝ) (hA : 0 ≤ A)
    (hχ : ∀ z, ‖d.χ z‖ ≤ A) (i : Fin (N + 1)) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) :
    ‖∫ p in nativeRegion N r, nativeDensity (current d) i r p‖ ≤
      (A * betaBound d * r * (1 + |Real.log r|)) *
        ∫ p in centeredRegion d, NormalCrossing.boundaryMajorant (fun _ : Fin N ↦ 1) p := by
  rw [nativeIntegral_eq_centeredIndicator d i r hr]
  have hm := (integrableOn_centeredMajorant d).const_mul (A * betaBound d * r * (1 + |Real.log r|))
  have hb : ∀ᵐ p ∂(volume.restrict (centeredRegion d)),
      ‖(nativeRegion N r).indicator (nativeDensity (current d) i r) p‖ ≤
        (A * betaBound d * r * (1 + |Real.log r|)) *
          NormalCrossing.boundaryMajorant (fun _ : Fin N ↦ 1) p := by
    filter_upwards [ae_restrict_mem (measurableSet_centeredRegion d)] with p hp
    exact (norm_indicator_le_norm_self (s := nativeRegion N r) (f := nativeDensity (current d) i r) (a := p)).trans
      (norm_nativeDensity_current_le d A hA hχ i r hr hr1 p
        (fun k ↦ norm_pos_iff.mp (hp.2 k trivial).1))
  have h := norm_integral_le_of_norm_le hm hb
  rwa [integral_const_mul] at h

/-- Boundary integrability is derived from the same actual majorant, not assumed. -/
theorem integrableOn_nativeDensity_current {N : ℕ} (d : LocalData N) (i : Fin (N + 1))
    (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) :
    IntegrableOn (nativeDensity (current d) i r) (nativeRegion N r) := by
  obtain ⟨A, B, hA, hB, hχ, hDχ⟩ := exists_cutoff_bounds d
  have hm := (integrableOn_centeredMajorant d).const_mul (A * betaBound d * r * (1 + |Real.log r|))
  have hf : IntegrableOn (nativeDensity (current d) i r) (centeredRegion d) := by
    apply hm.mono' ((continuousOn_nativeDensity_current d i hr).aestronglyMeasurable
      (measurableSet_centeredRegion d))
    filter_upwards [ae_restrict_mem (measurableSet_centeredRegion d)] with p hp
    exact norm_nativeDensity_current_le d A hA hχ i r hr hr1 p
      (fun k ↦ norm_pos_iff.mp (hp.2 k trivial).1)
  apply hf.of_forall_sdiff_eq_zero (measurableSet_nativeRegion N r)
  rintro p ⟨hp, hn⟩
  exact nativeDensity_zero_outside_centered d i r hr p hp hn

theorem tendsto_radius_logPolynomial :
    Tendsto (fun r : ℝ ↦ r * (1 + |Real.log r|)) (𝓝[>] 0) (𝓝 0) := by
  have h := (LogPole.tendsto_radius_mul_abs_log_pow 0).add (LogPole.tendsto_radius_mul_abs_log_pow 1)
  convert h using 1
  · funext r
    simp only [pow_zero, pow_one]
    ring
  · simp

/-- The genuine cylinder flux limit follows from the actual monomial and cutoff bounds. -/
theorem tendsto_nativeIntegral_current {N : ℕ} (d : LocalData N) (i : Fin (N + 1)) :
    Tendsto (fun r ↦ ∫ p in nativeRegion N r, nativeDensity (current d) i r p) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨A, B, hA, hB, hχ, hDχ⟩ := exists_cutoff_bounds d
  have hlim : Tendsto
      (fun r : ℝ ↦ (A * betaBound d * r * (1 + |Real.log r|)) *
        ∫ p in centeredRegion d, NormalCrossing.boundaryMajorant (fun _ : Fin N ↦ 1) p)
      (𝓝[>] 0) (𝓝 0) := by
    have h := (tendsto_radius_logPolynomial.const_mul (A * betaBound d)).mul_const
      (∫ p in centeredRegion d, NormalCrossing.boundaryMajorant (fun _ : Fin N ↦ 1) p)
    simpa only [mul_zero, zero_mul, mul_assoc] using h
  apply squeeze_zero_norm' _ hlim
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with r hr
  exact nativeIntegral_bound d A hA hχ i r hr.1 hr.2.le

/-- The actual local normal-crossing current theorem. No regularity, L¹,
support, or flux hypothesis for χβ is left to the caller. -/
theorem integral_extDeriv_current_eq_zero {N : ℕ} (d : LocalData N) :
    (∫ z : Space N, extDeriv (current d) z (frame N)) = 0 :=
  integral_extDeriv_eq_zero_of_native_limits (current d) (contDiffOn_current d)
    (hasCompactSupport_current d) (integrable_current_density d) (tendsto_nativeIntegral_current d)

theorem integrableOn_extDeriv_beta_coefficient {N : ℕ} (d : LocalData N)
    (v : Fin (Dim N) → Space N) (hv : ∀ j, ‖v j‖ ≤ 1) :
    IntegrableOn (fun z ↦ extDeriv (beta d) z v)
      (d.U ∩ NormalCrossing.puncturedPolydisc (fun _ : Fin (N + 1) ↦ d.ρ)) := by
  have hc : ContinuousOn (fun z ↦ extDeriv (beta d) z v)
      (d.U ∩ NormalCrossing.puncturedPolydisc (fun _ : Fin (N + 1) ↦ d.ρ)) := by
    intro z hz
    have hβ := contDiffAt_beta d ⟨hz.1, punctured_mem_polydisc hz.2⟩ (punctured_mem_regular hz.2)
    exact ((ContinuousAlternatingMap.apply ℝ _ ℝ v).continuous.continuousAt.comp
      ((ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ _ ℝ).continuous.continuousAt.comp
        (hβ.continuousAt_fderiv (by norm_num)))).continuousWithinAt
  have hm0 : IntegrableOn (fun z ↦ derivativeBound d * NormalCrossing.majorant (fun _ : Fin (N + 1) ↦ 0) z)
      (NormalCrossing.puncturedPolydisc (fun _ : Fin (N + 1) ↦ d.ρ)) :=
    (NormalCrossing.integrableOn_majorant (fun _ : Fin (N + 1) ↦ 0) (fun _ ↦ d.ρ)).const_mul (derivativeBound d)
  have hm := hm0.mono_set (inter_subset_right (s := d.U))
  apply hm.mono' (hc.aestronglyMeasurable (d.open_U.measurableSet.inter (NormalCrossing.measurableSet_puncturedPolydisc _)))
  filter_upwards [ae_restrict_mem (d.open_U.measurableSet.inter (NormalCrossing.measurableSet_puncturedPolydisc _))] with z hz
  exact norm_extDeriv_beta_coefficient_le d ⟨hz.1, punctured_mem_polydisc hz.2⟩ (punctured_mem_regular hz.2) v hv

/-- Unbundled local current theorem. The only smoothness assumptions concern
the actual cutoff and the actual units on their open domain. -/
theorem compact_monomial_stokes {N : ℕ}
    (a : Fin (Dim N) → Fin (N + 1) → ℤ) (u : Fin (Dim N) → Space N → ℂ)
    (χ : Space N → ℝ) (ρ D c M : ℝ) (hρ : 0 < ρ) (hc : 0 < c)
    (U : Set (Space N)) (hU : IsOpen U)
    (hχ : ContDiff ℝ 1 χ) (hcompact : HasCompactSupport χ)
    (hsupport_U : tsupport χ ⊆ U) (hsupport_ρ : tsupport χ ⊆ polydisc N ρ)
    (hu : ∀ j, ContDiffOn ℝ 2 (u j) U)
    (hunit : ∀ z ∈ U ∩ polydisc N ρ, ∀ j, c ≤ ‖u j z‖)
    (hD : ∀ z ∈ U ∩ polydisc N ρ, ∀ j, ‖fderiv ℝ (u j) z‖ ≤ D)
    (hupper : ∀ z ∈ U ∩ polydisc N ρ, ‖u 0 z‖ ≤ M) :
    (∫ z : Space N, extDeriv
      (fun x ↦ χ x • LogRadialPrimitive.primitive (LogMonomial.coordinateMonomial a u) x) z (frame N)) = 0 :=
  integral_extDeriv_current_eq_zero
    { a := a, u := u, χ := χ, ρ := ρ, D := D, c := c, M := M,
      ρ_pos := hρ, c_pos := hc, U := U, open_U := hU,
      cutoff_C1 := hχ, cutoff_compact := hcompact,
      support_U := hsupport_U, support_polydisc := hsupport_ρ,
      units_C2 := hu, unit_lower := hunit, unit_derivative := hD, first_unit_upper := hupper }

end EnvelopingIsomorphism.Deformation.Kontsevich.CompactMonomialStokes
