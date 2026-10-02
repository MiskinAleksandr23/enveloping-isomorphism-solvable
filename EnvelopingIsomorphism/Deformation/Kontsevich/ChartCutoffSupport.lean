import EnvelopingIsomorphism.Deformation.Kontsevich.CompactSmoothPartition
import Mathlib.Topology.OpenPartialHomeomorph.Continuity
import Mathlib.Topology.Algebra.Support

/-! Compact chart pullback supports and actual ambient smooth localization cutoffs. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.ChartCutoffSupport

open Set Function
open scoped Classical Topology Manifold ContDiff

section Chart

variable {X K : Type*} [TopologicalSpace X] [TopologicalSpace K]
    (e : OpenPartialHomeomorph X K) (ρ : K → ℝ)

/-- The actual inverse-chart image of the global support. -/
def pulledSupport : Set X := e.symm '' tsupport ρ

theorem pulledSupport_subset_source (hsub : tsupport ρ ⊆ e.target) :
    pulledSupport e ρ ⊆ e.source := by
  rintro x ⟨y, hy, rfl⟩
  exact e.map_target (hsub hy)

/-- Pull the global scalar piece into the chart and extend it by zero. -/
def zeroPullback (x : X) : ℝ := if x ∈ e.source then ρ (e x) else 0

@[simp] theorem zeroPullback_source {x : X} (hx : x ∈ e.source) :
    zeroPullback e ρ x = ρ (e x) := if_pos hx

@[simp] theorem zeroPullback_off_source {x : X} (hx : x ∉ e.source) :
    zeroPullback e ρ x = 0 := if_neg hx

theorem support_zeroPullback_subset : support (zeroPullback e ρ) ⊆ pulledSupport e ρ := by
  intro x hx
  have hn : zeroPullback e ρ x ≠ 0 := hx
  have hs : x ∈ e.source := by
    by_contra hs
    exact hn (zeroPullback_off_source e ρ hs)
  have hr : ρ (e x) ≠ 0 := by simpa only [zeroPullback_source e ρ hs] using hn
  exact ⟨e x, subset_tsupport ρ hr, e.left_inv hs⟩

variable [CompactSpace K]

/-- Compactness follows from the actual inverse chart's continuity on its target. -/
theorem isCompact_pulledSupport (hsub : tsupport ρ ⊆ e.target) : IsCompact (pulledSupport e ρ) :=
  (isClosed_tsupport ρ).isCompact.image_of_continuousOn (e.continuousOn_symm.mono hsub)

variable [T2Space X]

/-- The topological support lies in the actual compact inverse image, including
all boundary points of the zero extension. -/
theorem tsupport_zeroPullback_subset (hsub : tsupport ρ ⊆ e.target) :
    tsupport (zeroPullback e ρ) ⊆ pulledSupport e ρ :=
  closure_minimal (support_zeroPullback_subset e ρ) (isCompact_pulledSupport e ρ hsub).isClosed

theorem hasCompactSupport_zeroPullback (hsub : tsupport ρ ⊆ e.target) :
    HasCompactSupport (zeroPullback e ρ) :=
  (isCompact_pulledSupport e ρ hsub).of_isClosed_subset (isClosed_tsupport _)
    (tsupport_zeroPullback_subset e ρ hsub)

/-- Continuity across the chart boundary follows from the compact support being
strictly inside the actual open source. -/
theorem continuous_zeroPullback (hρ : Continuous ρ) (hsub : tsupport ρ ⊆ e.target) :
    Continuous (zeroPullback e ρ) := by
  apply continuous_of_tsupport
  intro x hx
  have hs : x ∈ e.source := pulledSupport_subset_source e ρ hsub
    (tsupport_zeroPullback_subset e ρ hsub hx)
  apply (hρ.continuousAt.comp (e.continuousAt hs)).congr_of_eventuallyEq
  filter_upwards [e.open_source.mem_nhds hs] with y hy
  exact zeroPullback_source e ρ hy

end Chart

section EuclideanCutoff

abbrev Euclidean (d : ℕ) := Fin d → ℝ

/-- A native singleton smooth partition constructs a compact smooth cutoff equal
to one on the prescribed compact set and supported in its actual open neighborhood. -/
theorem exists_smooth_cutoff {d : ℕ} (C U : Set (Euclidean d))
    (hC : IsCompact C) (hU : IsOpen U) (hCU : C ⊆ U) :
    ∃ κ : Euclidean d → ℝ, ContDiff ℝ ∞ κ ∧ HasCompactSupport κ ∧
      tsupport κ ⊆ U ∧ EqOn κ (fun _ => 1) C := by
  obtain ⟨O, η, hO, hCO, hOU, hsub, hcpt, hsm, hsum⟩ :=
    CompactSmoothPartition.exists_compact_smoothPartition C hC (fun _ : Unit => U)
      (fun _ => hU) (by intro x hx; exact mem_iUnion.mpr ⟨(), hCU hx⟩)
  refine ⟨fun x => η () x, hsm (), hcpt (), hsub (), ?_⟩
  intro x hx
  simpa using hsum x (hCO hx)

variable {d : ℕ} {S : Set (Euclidean d)} {K : Type*}
    [TopologicalSpace K] [CompactSpace K]
    (e : OpenPartialHomeomorph S K) (ρ : K → ℝ)

/-- Compactness also holds for the actual support viewed in the ambient Euclidean space. -/
theorem isCompact_ambientSupport (hsub : tsupport ρ ⊆ e.target) :
    IsCompact (Subtype.val '' pulledSupport e ρ : Set (Euclidean d)) :=
  (isCompact_pulledSupport e ρ hsub).image continuous_subtype_val

/-- For a closed Euclidean orthant (or any closed Euclidean subset), the actual
relatively open chart source has an ambient open extension and a constructed
smooth compact cutoff equal to one on the entire pulled global support. -/
theorem exists_ambient_chart_cutoff (hS : IsClosed S) (hsub : tsupport ρ ⊆ e.target) :
    ∃ (U : Set (Euclidean d)) (κ : Euclidean d → ℝ),
      IsOpen U ∧ (Subtype.val ⁻¹' U : Set S) = e.source ∧
      ContDiff ℝ ∞ κ ∧ HasCompactSupport κ ∧ tsupport κ ⊆ U ∧
      EqOn κ (fun _ => 1) (Subtype.val '' pulledSupport e ρ) := by
  obtain ⟨U, hU, hpre⟩ := hS.isClosedEmbedding_subtypeVal.isEmbedding.isInducing.isOpen_iff.mp e.open_source
  have hCU : (Subtype.val '' pulledSupport e ρ : Set (Euclidean d)) ⊆ U := by
    rintro x ⟨y, hy, rfl⟩
    change y ∈ (Subtype.val ⁻¹' U : Set S)
    rw [hpre]
    exact pulledSupport_subset_source e ρ hsub hy
  obtain ⟨κ, hκ, hcpt, hsupp, hone⟩ := exists_smooth_cutoff _ U (isCompact_ambientSupport e ρ hsub) hU hCU
  exact ⟨U, κ, hU, hpre, hκ, hcpt, hsupp, hone⟩

omit [CompactSpace K] in
/-- Subordination to the actual ambient source makes the cutoff vanish at every
orthant point outside the original chart source. -/
theorem cutoff_zero_off_source (U : Set (Euclidean d)) (κ : Euclidean d → ℝ)
    (hpre : (Subtype.val ⁻¹' U : Set S) = e.source) (hκ : tsupport κ ⊆ U)
    (x : S) (hx : x ∉ e.source) : κ x.val = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro hs
  apply hx
  rw [← hpre]
  exact hκ hs

/-- A cutoff equal to one on the pulled support preserves the full zero-extended
piece everywhere on the orthant, including outside the chart. -/
theorem cutoff_mul_zeroPullback (hsub : tsupport ρ ⊆ e.target)
    (κ : Euclidean d → ℝ) (hone : EqOn κ (fun _ => 1) (Subtype.val '' pulledSupport e ρ)) (x : S) :
    κ x.val * zeroPullback e ρ x = zeroPullback e ρ x := by
  by_cases hz : zeroPullback e ρ x = 0
  · simp [hz]
  · have hx : x ∈ pulledSupport e ρ :=
      tsupport_zeroPullback_subset e ρ hsub (subset_tsupport _ hz)
    rw [hone (mem_image_of_mem Subtype.val hx), one_mul]

/-- Multiplying any actual form extension by the ambient cutoff leaves its
partition-weighted chart piece unchanged on the whole orthant. -/
theorem cutoff_smul_piece {V : Type*} [AddCommMonoid V] [Module ℝ V]
    (hsub : tsupport ρ ⊆ e.target) (κ : Euclidean d → ℝ)
    (hone : EqOn κ (fun _ => 1) (Subtype.val '' pulledSupport e ρ))
    (F : Euclidean d → V) (x : S) :
    zeroPullback e ρ x • (κ x.val • F x.val) = zeroPullback e ρ x • F x.val := by
  rw [smul_smul, mul_comm, cutoff_mul_zeroPullback e ρ hsub κ hone x]

/-- An actual ambient extension of the chart pullback becomes the exact global
zero extension on the whole orthant after multiplication by the constructed cutoff. -/
theorem cutoff_mul_extension (hsub : tsupport ρ ⊆ e.target)
    (U : Set (Euclidean d)) (κ F : Euclidean d → ℝ)
    (hpre : (Subtype.val ⁻¹' U : Set S) = e.source) (hκ : tsupport κ ⊆ U)
    (hone : EqOn κ (fun _ => 1) (Subtype.val '' pulledSupport e ρ))
    (hF : ∀ x : S, x ∈ e.source → F x.val = ρ (e x)) (x : S) :
    κ x.val * F x.val = zeroPullback e ρ x := by
  by_cases hx : x ∈ e.source
  · rw [hF x hx, ← zeroPullback_source e ρ hx]
    exact cutoff_mul_zeroPullback e ρ hsub κ hone x
  · rw [cutoff_zero_off_source e U κ hpre hκ x hx, zero_mul, zeroPullback_off_source e ρ hx]

/-- Compact ambient smooth localization is constructed together with exact
agreement on the entire orthant, rather than supplied as a cutoff hypothesis. -/
theorem exists_ambient_chart_localization (hS : IsClosed S) (hsub : tsupport ρ ⊆ e.target) :
    ∃ (U : Set (Euclidean d)) (κ : Euclidean d → ℝ),
      IsOpen U ∧ (Subtype.val ⁻¹' U : Set S) = e.source ∧
      ContDiff ℝ ∞ κ ∧ HasCompactSupport κ ∧ tsupport κ ⊆ U ∧
      EqOn κ (fun _ => 1) (Subtype.val '' pulledSupport e ρ) ∧
      (∀ x : S, x ∉ e.source → κ x.val = 0) ∧
      (∀ x : S, κ x.val * zeroPullback e ρ x = zeroPullback e ρ x) := by
  obtain ⟨U, κ, hU, hpre, hsm, hcpt, hκ, hone⟩ := exists_ambient_chart_cutoff e ρ hS hsub
  exact ⟨U, κ, hU, hpre, hsm, hcpt, hκ, hone,
    fun x hx => cutoff_zero_off_source e U κ hpre hκ x hx,
    cutoff_mul_zeroPullback e ρ hsub κ hone⟩

end EuclideanCutoff

end EnvelopingIsomorphism.Deformation.Kontsevich.ChartCutoffSupport
