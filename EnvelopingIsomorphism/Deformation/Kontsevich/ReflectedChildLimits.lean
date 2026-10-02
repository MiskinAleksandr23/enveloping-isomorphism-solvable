import EnvelopingIsomorphism.Deformation.Kontsevich.ReflectedSubsetLimits
import EnvelopingIsomorphism.Deformation.Kontsevich.SubsetLimitPartitions

/-! Exact parent/child centering and radius formulas for mixed reflected
normalization. A real child uses the midpoint of its marked point and its
mirror. Thus all scale separation is proved on the same extracted subsequence,
even before restricting to the eventual reflected tree. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.ReflectedChildLimits

open Filter Topology ComplexConjugate
open SubsetNormalizedLimits (LargeSubset ShapeFamily inclusion)
open ReflectedSubsetNormalization
open scoped Classical

variable {I : Type*} [Fintype I]

def childCenter (σ : I → I) (hσ : Function.Involutive σ) (A B : LargeSubset I)
    (hBA : B.val ⊆ A.val) (x : A.val → ℂ) : ℂ :=
  if hb : IsStable σ B then
    (x (inclusion A B hBA (chosenAnchor σ hσ B)) +
      x (inclusion A B hBA (stableReflection σ B hb (chosenAnchor σ hσ B)))) / 2
  else x (inclusion A B hBA (chosenAnchor σ hσ B))

theorem continuous_childCenter (σ : I → I) (hσ : Function.Involutive σ) (A B : LargeSubset I)
    (hBA : B.val ⊆ A.val) : Continuous (childCenter σ hσ A B hBA) := by
  unfold childCenter
  split_ifs <;> fun_prop

/-- Both possible child centers are exact affine combinations of parent-normalized points. -/
theorem childCenter_normalized (σ : I → I) (hσ : Function.Involutive σ) (A B : LargeSubset I)
    (hBA : B.val ⊆ A.val) (p : I → ℂ) (hp : ∀ j, p (σ j) = conj (p j)) :
    childCenter σ hσ A B hBA (normalizedOn σ hσ A p) =
      (radiusOn σ hσ A p)⁻¹ • (centerOn σ hσ B p - centerOn σ hσ A p) := by
  by_cases hB : IsStable σ B
  · have hbcenter : centerOn σ hσ B p =
        (p (chosenAnchor σ hσ B) + p (σ (chosenAnchor σ hσ B).val)) / 2 := by
      rw [centerOn, if_pos hB, hp]
      exact Complex.re_eq_add_conj _
    rw [childCenter, dif_pos hB, normalizedOn_apply, normalizedOn_apply, hbcenter]
    change ((radiusOn σ hσ A p)⁻¹ • (p (chosenAnchor σ hσ B) - centerOn σ hσ A p) +
      (radiusOn σ hσ A p)⁻¹ • (p (σ (chosenAnchor σ hσ B).val) - centerOn σ hσ A p)) / 2 = _
    simp only [Complex.real_smul]
    ring
  · have hbcenter : centerOn σ hσ B p = p (chosenAnchor σ hσ B) := by
      simp only [centerOn, if_neg hB]
    rw [childCenter, dif_neg hB, normalizedOn_apply, hbcenter]
    rfl

/-- Exact radius cancellation, with the actual normalization used at both nodes. -/
theorem radius_ratio_eq_norm (σ : I → I) (hσ : Function.Involutive σ) (A B : LargeSubset I)
    (hBA : B.val ⊆ A.val) (p : I → ℂ) (hp : ∀ j, p (σ j) = conj (p j)) :
    radiusOn σ hσ B p / radiusOn σ hσ A p =
      ‖fun j : B.val => normalizedOn σ hσ A p (inclusion A B hBA j) -
        childCenter σ hσ A B hBA (normalizedOn σ hσ A p)‖ := by
  have hfun : (fun j : B.val => normalizedOn σ hσ A p (inclusion A B hBA j) -
      childCenter σ hσ A B hBA (normalizedOn σ hσ A p)) =
      (radiusOn σ hσ A p)⁻¹ • (fun j : B.val => p j - centerOn σ hσ B p) := by
    funext j
    rw [normalizedOn_apply, childCenter_normalized σ hσ A B hBA p hp, ← smul_sub]
    change (radiusOn σ hσ A p)⁻¹ •
      ((p j - centerOn σ hσ A p) - (centerOn σ hσ B p - centerOn σ hσ A p)) = _
    congr 1
    abel_nf
  rw [hfun, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (radiusOn_nonneg σ hσ A p)),
    ← radiusOn_eq_norm σ hσ B p]
  exact div_eq_inv_mul _ _

theorem childCenter_eq_of_constant (σ : I → I) (hσ : Function.Involutive σ) (A B : LargeSubset I)
    (hBA : B.val ⊆ A.val) (q : A.val → ℂ)
    (hq : ∀ j : B.val, q (inclusion A B hBA j) = q (inclusion A B hBA (chosenAnchor σ hσ B))) :
    childCenter σ hσ A B hBA q = q (inclusion A B hBA (chosenAnchor σ hσ B)) := by
  unfold childCenter
  split_ifs with hB
  · rw [hq (stableReflection σ B hB (chosenAnchor σ hσ B))]
    ring
  · rfl

/-- Actual normalized center offsets converge to the parent's child-shape value. -/
theorem center_offset_tendsto (σ : I → I) (hσ : Function.Involutive σ)
    (p : ℕ → I → ℂ) (hp : ∀ k j, p k (σ j) = conj (p k j)) (φ : ℕ → ℕ)
    (A B : LargeSubset I) (hBA : B.val ⊆ A.val) (q : A.val → ℂ)
    (hlim : Tendsto (fun k => normalizedOn σ hσ A (p (φ k))) atTop (𝓝 q))
    (hq : ∀ j : B.val, q (inclusion A B hBA j) = q (inclusion A B hBA (chosenAnchor σ hσ B))) :
    Tendsto (fun k => (radiusOn σ hσ A (p (φ k)))⁻¹ •
      (centerOn σ hσ B (p (φ k)) - centerOn σ hσ A (p (φ k)))) atTop
        (𝓝 (q (inclusion A B hBA (chosenAnchor σ hσ B)))) := by
  have h := ((continuous_childCenter σ hσ A B hBA).tendsto q).comp hlim
  simpa only [Function.comp_def, childCenter_normalized σ hσ A B hBA _ (hp _),
    childCenter_eq_of_constant σ hσ A B hBA q hq] using h

/-- A genuine reflected child radius vanishes relative to its parent on the very same subsequence. -/
theorem radius_ratio_tendsto_zero (σ : I → I) (hσ : Function.Involutive σ)
    (p : ℕ → I → ℂ) (hp : ∀ k j, p k (σ j) = conj (p k j)) (φ : ℕ → ℕ)
    (A B : LargeSubset I) (hBA : B.val ⊆ A.val) (q : A.val → ℂ)
    (hlim : Tendsto (fun k => normalizedOn σ hσ A (p (φ k))) atTop (𝓝 q))
    (hq : ∀ j : B.val, q (inclusion A B hBA j) = q (inclusion A B hBA (chosenAnchor σ hσ B))) :
    Tendsto (fun k => radiusOn σ hσ B (p (φ k)) / radiusOn σ hσ A (p (φ k))) atTop (𝓝 0) := by
  have hc : Continuous (fun x : A.val → ℂ =>
      (fun j : B.val => x (inclusion A B hBA j) - childCenter σ hσ A B hBA x)) :=
    continuous_pi fun j => (continuous_apply _).sub (continuous_childCenter σ hσ A B hBA)
  have h := ((hc.tendsto q).comp hlim).norm
  have hz : (fun j : B.val => q (inclusion A B hBA j) - childCenter σ hσ A B hBA q) = 0 := by
    funext j
    rw [childCenter_eq_of_constant σ hσ A B hBA q hq, hq j, sub_self]
    rfl
  have heq : (fun k => radiusOn σ hσ B (p (φ k)) / radiusOn σ hσ A (p (φ k))) =
      fun k => ‖fun j : B.val => normalizedOn σ hσ A (p (φ k)) (inclusion A B hBA j) -
        childCenter σ hσ A B hBA (normalizedOn σ hσ A (p (φ k)))‖ :=
    funext fun k => radius_ratio_eq_norm σ hσ A B hBA (p (φ k)) (hp (φ k))
  rw [heq]
  simpa only [Function.comp_def, hz, norm_zero] using h

end EnvelopingIsomorphism.Deformation.Kontsevich.ReflectedChildLimits
