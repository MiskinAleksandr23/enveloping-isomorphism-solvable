import EnvelopingIsomorphism.Deformation.Kontsevich.NormalizedClusterLimits
import Mathlib.Data.Fintype.Powerset

/-!
# Simultaneous normalized limits on every nontrivial finite subset

A single compactness argument in a finite product of genuine unit spheres
extracts one common subsequence for all subsets. Subsequent tree recursion
therefore never needs an additional subsequence choice. The input is only an
actual sequence of injective complex configurations.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.SubsetNormalizedLimits

open Filter Topology
open scoped Classical

variable {I : Type*} [Fintype I]

abbrev LargeSubset (I : Type*) [Fintype I] := {A : Finset I // 1 < A.card}

instance (A : LargeSubset I) : Nontrivial A.val := by
  apply Fintype.one_lt_card_iff_nontrivial.mp
  simpa using A.property

def anchor (A : LargeSubset I) : A.val := Classical.ofNonempty

def normalizedOn (A : LargeSubset I) (p : I → ℂ) : A.val → ℂ :=
  NormalizedClusterLimits.normalized (anchor A) (fun j : A.val => p j)

def radiusOn (A : LargeSubset I) (p : I → ℂ) : ℝ :=
  NormalizedClusterLimits.radius (anchor A) (fun j : A.val => p j)

abbrev ShapeFamily (I : Type*) [Fintype I] := ∀ A : LargeSubset I, A.val → ℂ

theorem normalizedOn_mem_sphere (A : LargeSubset I) (p : I → ℂ) (hp : Function.Injective p) :
    normalizedOn A p ∈ Metric.sphere (0 : A.val → ℂ) 1 :=
  NormalizedClusterLimits.normalized_mem_sphere (anchor A) (fun j : A.val => p j)
    (hp.comp Subtype.val_injective)

/-- Compactness for all normalized finite subsets at once. -/
theorem isCompact_shapeSpheres :
    IsCompact {q : ShapeFamily I | ∀ A : LargeSubset I, q A ∈ Metric.sphere (0 : A.val → ℂ) 1} :=
  isCompact_pi_infinite fun A : LargeSubset I => isCompact_sphere (0 : A.val → ℂ) 1

/-- The common subsequence and every normalized limit are constructed from the input sequence. -/
theorem exists_common_normalized_limits (p : ℕ → I → ℂ) (hp : ∀ k, Function.Injective (p k)) :
    ∃ (φ : ℕ → ℕ) (q : ShapeFamily I), StrictMono φ ∧
      ∀ A : LargeSubset I,
        Tendsto (fun k => normalizedOn A (p (φ k))) atTop (𝓝 (q A)) ∧
        q A (anchor A) = 0 ∧ ‖q A‖ = 1 ∧ ∃ j k, q A j ≠ q A k := by
  obtain ⟨q, hq, φ, hφ, hlim⟩ := (isCompact_shapeSpheres (I := I)).tendsto_subseq
    (fun (k : ℕ) (A : LargeSubset I) => normalizedOn_mem_sphere A (p k) (hp k))
  refine ⟨φ, q, hφ, fun A => ?_⟩
  have hA : Tendsto (fun k => normalizedOn A (p (φ k))) atTop (𝓝 (q A)) :=
    (continuous_apply A).tendsto q |>.comp hlim
  have hanchor : q A (anchor A) = 0 := by
    have h := (continuous_apply (anchor A)).tendsto (q A) |>.comp hA
    have hz : Tendsto (fun k => normalizedOn A (p (φ k)) (anchor A)) atTop (𝓝 (0 : ℂ)) := by
      simpa only [normalizedOn, NormalizedClusterLimits.normalized_anchor] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0))
    exact tendsto_nhds_unique h hz
  have hnorm : ‖q A‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hq A
  exact ⟨hA, hanchor, hnorm, NormalizedClusterLimits.nonconstant_of_normalized (anchor A) (q A) hanchor hnorm⟩

/-- Exact child-radius separation for any constant limit block, on that same subsequence. -/
theorem child_ratio_tendsto_zero (p : ℕ → I → ℂ) (φ : ℕ → ℕ) (q : ShapeFamily I)
    (A : LargeSubset I)
    (hlim : Tendsto (fun k => normalizedOn A (p (φ k))) atTop (𝓝 (q A)))
    (B : Finset A.val) (b : A.val) (hB : ∀ j ∈ B, q A j = q A b) :
    Tendsto (fun k => NormalizedClusterLimits.childRadius B b
      (fun j : A.val => p (φ k) j) / radiusOn A (p (φ k))) atTop (𝓝 0) :=
  NormalizedClusterLimits.child_ratio_tendsto_zero B (anchor A) b
    (fun k j => p k j) φ (q A) hlim hB

def inclusion (A B : LargeSubset I) (hBA : B.val ⊆ A.val) : B.val → A.val :=
  fun j => ⟨j.val, hBA j.property⟩

/-- Parent and child can use their own fixed marked labels: the radius ratio
is still exactly the norm of the relative normalized child array. -/
theorem radius_ratio_eq_norm (A B : LargeSubset I) (hBA : B.val ⊆ A.val) (p : I → ℂ) :
    radiusOn B p / radiusOn A p =
      ‖fun j : B.val => normalizedOn A p (inclusion A B hBA j) -
        normalizedOn A p (inclusion A B hBA (anchor B))‖ := by
  have hfun : (fun j : B.val => normalizedOn A p (inclusion A B hBA j) -
      normalizedOn A p (inclusion A B hBA (anchor B))) =
      (radiusOn A p)⁻¹ • NormalizedClusterLimits.centered (anchor B) (fun j : B.val => p j) := by
    funext j
    exact NormalizedClusterLimits.normalized_sub (anchor A)
      (inclusion A B hBA j) (inclusion A B hBA (anchor B)) (fun j : A.val => p j)
  have hnonneg : 0 ≤ radiusOn A p := norm_nonneg _
  rw [hfun, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hnonneg)]
  exact div_eq_inv_mul _ _

/-- Every constant limiting child has vanishing relative scale on the common subsequence. -/
theorem radius_ratio_tendsto_zero (p : ℕ → I → ℂ) (φ : ℕ → ℕ) (q : ShapeFamily I)
    (A B : LargeSubset I) (hBA : B.val ⊆ A.val)
    (hlim : Tendsto (fun k => normalizedOn A (p (φ k))) atTop (𝓝 (q A)))
    (hq : ∀ j : B.val, q A (inclusion A B hBA j) = q A (inclusion A B hBA (anchor B))) :
    Tendsto (fun k => radiusOn B (p (φ k)) / radiusOn A (p (φ k))) atTop (𝓝 0) := by
  have hc : Continuous (fun x : A.val → ℂ =>
      (fun j : B.val => x (inclusion A B hBA j) - x (inclusion A B hBA (anchor B)))) :=
    continuous_pi fun j => (continuous_apply _).sub (continuous_apply _)
  have h := ((hc.tendsto (q A)).comp hlim).norm
  have hz : (fun j : B.val => q A (inclusion A B hBA j) -
      q A (inclusion A B hBA (anchor B))) = 0 := funext fun j => sub_eq_zero.mpr (hq j)
  have heq : (fun k => radiusOn B (p (φ k)) / radiusOn A (p (φ k))) =
      fun k => ‖fun j : B.val => normalizedOn A (p (φ k)) (inclusion A B hBA j) -
        normalizedOn A (p (φ k)) (inclusion A B hBA (anchor B))‖ :=
    funext fun k => radius_ratio_eq_norm A B hBA (p (φ k))
  rw [heq]
  simpa only [Function.comp_def, hz, norm_zero] using h

end EnvelopingIsomorphism.Deformation.Kontsevich.SubsetNormalizedLimits
