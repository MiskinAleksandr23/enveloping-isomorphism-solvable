import EnvelopingIsomorphism.Deformation.Kontsevich.SimpleFaceZeroNodeLabels

/-! An arbitrary native forest representation of a first-order collision with
one coarse fiber has exactly one zero node, carrying that whole fiber. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Kontsevich.SingleStaticCollisionZeroNodeLabels

open Configuration ExtractedForestParameters ExtractedForestChildShapes ExtractedForestFrames
open ForestDirectionRatioCoordinates ReflectedRadiusCoordinates ForestRadialFaceClassification
open scoped Classical

theorem normalizedNormRatio_zero_iff (a b : ℂ) :
    (normalizedNormRatio a b : ℝ) = 0 ↔ a = 0 := by
  constructor
  · intro h
    by_contra ha
    exact (div_pos (norm_pos_iff.mpr ha)
      (add_pos_of_pos_of_nonneg (norm_pos_iff.mpr ha) (norm_nonneg b))).ne' h
  · intro h
    simp [normalizedNormRatio, h]

theorem linearRatioLimit_zero_iff (a b v w : ℂ) (hv : a = 0 → v ≠ 0) :
    (linearRatioLimit a b v w : ℝ) = 0 ↔ a = 0 ∧ b ≠ 0 := by
  by_cases h : a = 0 ∧ b = 0
  · rw [linearRatioLimit, if_pos h, normalizedNormRatio_zero_iff]
    simp [h.1, h.2, hv h.1]
  · rw [linearRatioLimit, if_neg h, normalizedNormRatio_zero_iff]
    tauto

variable {n m : ℕ} (C : Finset (DoubledLabel (n + 1) m))
  (B V : DoubledLabel (n + 1) m → ℂ)
  (hB : ∀ p : DoubledPair (n + 1) m, B p.val.2 - B p.val.1 = 0 ↔ p.val.1 ∈ C ∧ p.val.2 ∈ C)
  (hV : ∀ p : DoubledPair (n + 1) m, B p.val.2 - B p.val.1 = 0 → V p.val.2 - V p.val.1 ≠ 0)

include hB hV in
theorem linear_ratio_zero_iff (t : DoubledTriple (n + 1) m) :
    ((projectDR (linearCollisionCoordinates B V)).2 t : ℝ) = 0 ↔
      t.val.1 ∈ C ∧ t.val.2.1 ∈ C ∧ t.val.2.2 ∉ C := by
  change (linearRatioLimit _ _ _ _ : ℝ) = 0 ↔ _
  rw [linearRatioLimit_zero_iff _ _ _ _ (hV ⟨(t.val.1,t.val.2.1),t.property.1⟩)]
  have hp := hB ⟨(t.val.1,t.val.2.1),t.property.1⟩
  have hq := hB ⟨(t.val.1,t.val.2.2),t.property.2⟩
  constructor
  · rintro ⟨hz,hn⟩
    obtain ⟨ha,hb⟩ := hp.mp hz
    exact ⟨ha,hb,fun hc => hn (hq.mpr ⟨ha,hc⟩)⟩
  · rintro ⟨ha,hb,hc⟩
    exact ⟨hp.mpr ⟨ha,hb⟩, fun hz => hc (hq.mp hz).2⟩

include hB hV in
theorem label_eq_of_cross_ratios (A : Finset (DoubledLabel (n + 1) m))
    (hA : 1 < A.card) (hproper : A ≠ Finset.univ)
    (hzero : ∀ a ∈ A, ∀ b ∈ A, ∀ c, c ∉ A → ∀ (hab : a ≠ b) (hac : a ≠ c),
      ((projectDR (linearCollisionCoordinates B V)).2 ⟨(a,b,c),hab,hac⟩ : ℝ) = 0) : A = C := by
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hA
  have hout : ∃ c, c ∉ A := by
    by_contra h
    apply hproper
    ext j
    simp only [Finset.mem_univ, iff_true]
    by_contra hj
    exact h ⟨j,hj⟩
  obtain ⟨c,hc⟩ := hout
  have hac : a ≠ c := fun he => hc (he ▸ ha)
  have haC := ((linear_ratio_zero_iff C B V hB hV _).mp (hzero a ha b hb c hc hab hac)).1
  ext d
  constructor
  · intro hd
    by_cases had : a = d
    · exact had ▸ haC
    · exact ((linear_ratio_zero_iff C B V hB hV _).mp (hzero a ha d hd c hc had hac)).2.1
  · intro hd
    by_contra hdA
    have had : a ≠ d := fun he => hdA (he ▸ ha)
    exact ((linear_ratio_zero_iff C B V hB hV _).mp (hzero a ha b hb d hdA hab had)).2.2 hd

variable (x : Compactification (0 : Fin (n + 1)) m)
  (p : Domain (tree 0 x) (canonicalLeaf 0 x))
  (hDR : doubledCoordinates (tree 0 x) (canonicalLeaf 0 x) p = projectDR (linearCollisionCoordinates B V))

include hDR in
theorem ratioValue_eq_linear (t : DoubledTriple (n + 1) m) :
    ratioValue (tree 0 x) (canonicalLeaf 0 x) p.val t =
      ((projectDR (linearCollisionCoordinates B V)).2 t : ℝ) :=
  congrArg (fun d : DRData (n + 1) m => (d.2 t : ℝ)) hDR

include hB hV hDR in
theorem zero_node_label (v : ActiveNode (tree 0 x)) (hv : p.val.1 v.val = 0) : v.val.val = C := by
  apply label_eq_of_cross_ratios C B V hB hV v.val.val
    (ExtractedForestIdentification.nonleaf_large 0 x v.val v.property.2)
    (fun he => v.property.1 (Subtype.ext he))
  intro a ha b hb c hc hab hac
  rw [← ratioValue_eq_linear B V x p hDR]
  exact ForestResolvedRatioZero.ratioValue_eq_zero_of_zero_ancestor
    (tree 0 x) (canonicalLeaf 0 x) p v.val hv a b c hab hac
    ((le_canonicalLeaf_iff 0 x v.val a).mpr ha)
    ((le_canonicalLeaf_iff 0 x v.val b).mpr hb)
    (fun h => hc ((le_canonicalLeaf_iff 0 x v.val c).mp h))

include hB hV hDR in
theorem exists_unique_zero_node (hC : 1 < C.card) (hproper : C ≠ Finset.univ) :
    ∃ u : ActiveNode (tree 0 x), u.val.val = C ∧ p.val.1 u.val = 0 ∧
      ∀ v : ActiveNode (tree 0 x), v ≠ u → 0 < p.val.1 v.val := by
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hC
  have hout : ∃ c, c ∉ C := by
    by_contra h
    apply hproper
    ext j
    simp only [Finset.mem_univ, iff_true]
    by_contra hj
    exact h ⟨j,hj⟩
  obtain ⟨c,hc⟩ := hout
  have hac : a ≠ c := fun he => hc (he ▸ ha)
  let t : DoubledTriple (n + 1) m := ⟨(a,b,c),hab,hac⟩
  have hz : ratioValue (tree 0 x) (canonicalLeaf 0 x) p.val t = 0 := by
    rw [ratioValue_eq_linear B V x p hDR]
    exact (linear_ratio_zero_iff C B V hB hV t).mpr ⟨ha,hb,hc⟩
  obtain ⟨v,hlow,hhigh,hv⟩ := (ForestResolvedRatioZero.ratioValue_eq_zero_iff_exists_zero_between
    (tree 0 x) (canonicalLeaf 0 x) p t).mp hz
  have hactive : Active (tree 0 x) v := by
    refine ⟨fun he => ?_, ?_⟩
    · rw [he] at hlow
      exact not_lt_bot hlow
    · intro hmax
      have hpair := ForestLeafRadii.pairNode_nonleaf (tree 0 x) (canonicalLeaf 0 x)
        (canonicalLeaf_injective 0 x) (canonicalLeaf_isMax 0 x) (firstPair t)
      have he : v = pairNode (tree 0 x) (canonicalLeaf 0 x) (firstPair t) :=
        le_antisymm hhigh (hmax hhigh)
      exact hpair (he ▸ hmax)
  let u : ActiveNode (tree 0 x) := ⟨v,hactive⟩
  have hu : u.val.val = C := zero_node_label C B V hB hV x p hDR u hv
  refine ⟨u,hu,hv,?_⟩
  intro w hw
  have hn : p.val.1 w.val ≠ 0 := by
    intro hz
    exact hw (Subtype.ext (Subtype.ext ((zero_node_label C B V hB hV x p hDR w hz).trans hu.symm)))
  exact lt_of_le_of_ne (p.property.1 w.val) hn.symm

/-- Reflection stability of the primitive mask makes the unique zero node
fixed by the chart's actual reflection. -/
theorem node_fixed_of_mask (hC : C.image doubledReflection = C)
    (v : ActiveNode (tree 0 x)) (hv : v.val.val = C) : reflection 0 x v.val = v.val := by
  apply Subtype.ext
  rw [reflection_label, hv, hC]

end EnvelopingIsomorphism.Deformation.Kontsevich.SingleStaticCollisionZeroNodeLabels
