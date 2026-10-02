import EnvelopingIsomorphism.Deformation.Kontsevich.ReflectedSubsetLimits
import EnvelopingIsomorphism.Deformation.Kontsevich.SubsetLimitPartitions

/-! Reflection equivariance of the actual equal-limit finite partitions.
The equivariance is derived from the proved normalized shape relation. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.ReflectedSubsetPartitions

open ComplexConjugate SubsetNormalizedLimits ReflectedSubsetNormalization ReflectedSubsetLimits
open scoped Classical

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem reflectLargeSubset_val_eq_image (σ : I → I) (hσ : Function.Involutive σ) (A : LargeSubset I) :
    (reflectLargeSubset σ hσ A).val = A.val.image σ := by
  ext j
  change j ∈ (ReflectedClusterAnchors.reflectSubset σ (toNonemptySubset A)).val ↔ j ∈ A.val.image σ
  rw [ReflectedClusterAnchors.mem_reflectSubset_iff σ hσ (toNonemptySubset A), Finset.mem_image]
  constructor
  · intro hj
    exact ⟨σ j, hj, hσ j⟩
  · rintro ⟨k, hk, rfl⟩
    simpa only [hσ k, toNonemptySubset] using hk

theorem extendedShape_mirror (σ : I → I) (hσ : Function.Involutive σ)
    (q : ShapeFamily I) (hq : MirrorCompatible σ hσ q) (A : LargeSubset I) (j : I) :
    extendedShape q (reflectLargeSubset σ hσ A) (σ j) = conj (extendedShape q A j) := by
  by_cases hj : j ∈ A.val
  · have hrj : σ j ∈ (reflectLargeSubset σ hσ A).val := by
      rw [reflectLargeSubset_val_eq_image]
      exact Finset.mem_image.mpr ⟨j, hj, rfl⟩
    simpa only [extendedShape, dif_pos hj, dif_pos hrj, reflectIndex] using hq A ⟨j, hj⟩
  · have hrj : σ j ∉ (reflectLargeSubset σ hσ A).val := by
      intro h
      rw [reflectLargeSubset_val_eq_image] at h
      obtain ⟨k, hk, he⟩ := Finset.mem_image.mp h
      exact hj (hσ.injective he ▸ hk)
    simp only [extendedShape, dif_neg hj, dif_neg hrj, map_zero]

omit [Fintype I] in
theorem image_equalValue_fiber (σ : I → I) (A : Finset I) (f g : I → ℂ)
    (hfg : ∀ j, g (σ j) = conj (f j)) (b : I) :
    (A.filter (fun j => f b = f j)).image σ =
      (A.image σ).filter (fun j => g (σ b) = g j) := by
  ext j
  constructor
  · intro hj
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
    have hk' := Finset.mem_filter.mp hk
    refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨k, hk'.1, rfl⟩, ?_⟩
    rw [hfg, hfg, hk'.2]
  · intro hj
    obtain ⟨hjA, hjf⟩ := Finset.mem_filter.mp hj
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hjA
    refine Finset.mem_image.mpr ⟨k, Finset.mem_filter.mpr ⟨hk, ?_⟩, rfl⟩
    rw [hfg, hfg] at hjf
    exact (starRingEnd ℂ).injective hjf

/-- Native partition parts commute with reflection, including the singleton base case. -/
theorem partition_parts_mirror (σ : I → I) (hσ : Function.Involutive σ)
    (q : ShapeFamily I) (hq : MirrorCompatible σ hσ q) (A : Finset I) :
    (partition q (A.image σ)).parts = (partition q A).parts.image (Finset.image σ) := by
  have hcard : (A.image σ).card = A.card := Finset.card_image_of_injective A hσ.injective
  by_cases hA : 1 < A.card
  · have hRA : 1 < (A.image σ).card := by rwa [hcard]
    let B : LargeSubset I := ⟨A, hA⟩
    let C : LargeSubset I := ⟨A.image σ, hRA⟩
    have hBC : reflectLargeSubset σ hσ B = C := Subtype.ext (reflectLargeSubset_val_eq_image σ hσ B)
    let f := extendedShape q B
    let g := extendedShape q C
    have hfg : ∀ j, g (σ j) = conj (f j) := by
      intro j
      change extendedShape q C (σ j) = conj (extendedShape q B j)
      rw [← hBC]
      exact extendedShape_mirror σ hσ q hq B j
    rw [partition, dif_pos hRA, partition, dif_pos hA]
    change (A.image σ).image (fun b => (A.image σ).filter (fun j => g b = g j)) =
      (A.image (fun b => A.filter (fun j => f b = f j))).image (Finset.image σ)
    rw [Finset.image_image, Finset.image_image]
    apply Finset.image_congr
    intro b hb
    exact (image_equalValue_fiber σ A f g hfg b).symm
  · have hRA : ¬1 < (A.image σ).card := by rwa [hcard]
    rw [partition, dif_neg hRA, partition, dif_neg hA, Finpartition.parts_bot, Finpartition.parts_bot]
    simp only [Finset.map_eq_image, Finset.image_image, Function.Embedding.coeFn_mk]
    apply Finset.image_congr
    intro b hb
    simp only [Function.comp_apply, Finset.image_singleton]

end EnvelopingIsomorphism.Deformation.Kontsevich.ReflectedSubsetPartitions
