import EnvelopingIsomorphism.Deformation.Kontsevich.ExtractedForestParameters
import EnvelopingIsomorphism.Deformation.Kontsevich.LinearCollisionLimits

/-! Stored triple ratios detect collisions in every actual extracted subset
shape. In particular positive internal ratios rule out further large parts. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Kontsevich.ExtractedShapeRatios

open Configuration Filter Topology ExtractedForestParameters
open SubsetNormalizedLimits (LargeSubset)
open ReflectedSubsetNormalization
open scoped Classical

variable {n m : ℕ} (i : Fin n) (x : Compactification i m)

theorem ratio_eq (A : LargeSubset (DoubledLabel n m)) (a b c : A.val)
    (hab : a.val ≠ b.val) (hac : a.val ≠ c.val)
    (hne : ¬ ((extraction i x).shapes A b = (extraction i x).shapes A a ∧
      (extraction i x).shapes A c = (extraction i x).shapes A a)) :
    x.val.2.2 ⟨(a.val, b.val, c.val), hab, hac⟩ =
      normalizedNormRatio ((extraction i x).shapes A b - (extraction i x).shapes A a)
        ((extraction i x).shapes A c - (extraction i x).shapes A a) := by
  let q := (extraction i x).shapes A
  have hlim (j : A.val) : Tendsto
      (fun k => normalizedOn doubledReflection doubledReflection_involutive A (point i x k) j)
      atTop (𝓝 (q j)) :=
    (continuous_apply j).continuousAt.tendsto.comp ((extraction i x).limits A)
  have hr := (continuousAt_normalizedNormRatio (q b - q a) (q c - q a)
    (by simpa only [sub_eq_zero] using hne)).tendsto.comp
      (((hlim b).sub (hlim a)).prodMk_nhds ((hlim c).sub (hlim a)))
  have he (k : ℕ) :
      normalizedNormRatio
        (normalizedOn doubledReflection doubledReflection_involutive A (point i x k) b -
          normalizedOn doubledReflection doubledReflection_involutive A (point i x k) a)
        (normalizedOn doubledReflection doubledReflection_involutive A (point i x k) c -
          normalizedOn doubledReflection doubledReflection_involutive A (point i x k) a) =
      (normalizedSequence i x ((extraction i x).subsequence k)).val.tripleDistanceRatio
        ⟨(a.val, b.val, c.val), hab, hac⟩ := by
    rw [normalizedOn_sub, normalizedOn_sub]
    rw [Complex.real_smul, Complex.real_smul,
      normalizedNormRatio_pos_real_mul _
        (inv_pos.mpr (radiusOn_pos _ _ _ _ (point_injective i x k)))]
    rfl
  have hr' : Tendsto
      (fun k => (normalizedSequence i x ((extraction i x).subsequence k)).val.tripleDistanceRatio
        ⟨(a.val, b.val, c.val), hab, hac⟩) atTop
      (𝓝 (normalizedNormRatio (q b - q a) (q c - q a))) := by
    convert hr using 1
    funext k
    exact (he k).symm
  exact tendsto_nhds_unique
    (ReflectedForestExtraction.compactificationExtraction_ratios i x _) hr'

theorem shapes_injective_of_ratios_pos (A : LargeSubset (DoubledLabel n m))
    (hpos : ∀ (a b c : A.val) (hab : a.val ≠ b.val) (hac : a.val ≠ c.val),
      0 < (x.val.2.2 ⟨(a.val, b.val, c.val), hab, hac⟩ : ℝ)) :
    Function.Injective ((extraction i x).shapes A) := by
  intro a b he
  by_contra hab
  have hab' : a.val ≠ b.val := fun h => hab (Subtype.ext h)
  obtain ⟨u, v, huv⟩ := (extraction i x).shapes_nonconstant A
  have hc : ∃ c : A.val, (extraction i x).shapes A c ≠ (extraction i x).shapes A a := by
    by_cases hu : (extraction i x).shapes A u = (extraction i x).shapes A a
    · exact ⟨v, fun hv => huv (hu.trans hv.symm)⟩
    · exact ⟨u, hu⟩
  obtain ⟨c, hc⟩ := hc
  have hac : a.val ≠ c.val := fun h => hc (congrArg _ (Subtype.ext h.symm))
  have hr := ratio_eq i x A a b c hab' hac (fun h => hc h.2)
  have hz := hpos a b c hab' hac
  rw [hr] at hz
  simp [normalizedNormRatio, he] at hz

theorem part_card_le_one_of_shapes_injective (A : LargeSubset (DoubledLabel n m))
    (hinj : Function.Injective ((extraction i x).shapes A))
    (B : Finset (DoubledLabel n m)) (hB : B ∈ ((extraction i x).partitions A.val).parts) :
    B.card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro a ha b hb
  have hsub := ((extraction i x).partitions A.val).le hB
  exact congrArg Subtype.val (hinj (SubsetNormalizedLimits.eq_shape_of_mem_same_part
    (extraction i x).shapes A hB ⟨a, hsub ha⟩ ⟨b, hsub hb⟩ ha hb))

end EnvelopingIsomorphism.Deformation.Kontsevich.ExtractedShapeRatios
