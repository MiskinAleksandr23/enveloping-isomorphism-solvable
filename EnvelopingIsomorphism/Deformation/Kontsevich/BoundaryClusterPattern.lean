import EnvelopingIsomorphism.Deformation.Kontsevich.BoundaryClusterData

/-! The exact fixed collision mask for a real-boundary cluster. Original
interior labels, their conjugates, and the real boundary block all collapse
together. Every doubled label outside this mask retains a distinct base. -/

namespace EnvelopingIsomorphism.Deformation.Kontsevich

open Configuration ComplexConjugate

def boundaryClusterCollapses {n m : ℕ} (S : Finset (Fin n)) (l u : Fin (m + 1)) :
    DoubledLabel n m → Prop
  | Sum.inl (Sum.inl j) => j ∈ S
  | Sum.inl (Sum.inr j) => j ∈ boundaryClusterBlock l u
  | Sum.inr j => j ∈ S

instance {n m : ℕ} (S : Finset (Fin n)) (l u : Fin (m + 1)) (v : DoubledLabel n m) :
    Decidable (boundaryClusterCollapses S l u v) := by
  unfold boundaryClusterCollapses
  split <;> infer_instance

def boundaryClusterPairCollapses {n m : ℕ} (S : Finset (Fin n)) (l u : Fin (m + 1))
    (p : DoubledPair n m) : Prop :=
  boundaryClusterCollapses S l u p.val.1 ∧ boundaryClusterCollapses S l u p.val.2

instance {n m : ℕ} (S : Finset (Fin n)) (l u : Fin (m + 1)) (p : DoubledPair n m) :
    Decidable (boundaryClusterPairCollapses S l u p) := inferInstanceAs (Decidable (_ ∧ _))

namespace BoundaryClusterData

variable {n m : ℕ} {i a : Fin n} {S : Finset (Fin n)} {l u : Fin (m + 1)}

theorem base_eq_center_iff (D : BoundaryClusterData i a m S l u) (j : Fin n) :
    D.base j = (D.center : ℂ) ↔ j ∈ S := by
  constructor
  · intro h
    by_contra hj
    have hpos := D.base_im_pos_off j hj
    rw [h, Complex.ofReal_im] at hpos
    exact lt_irrefl _ hpos
  · exact D.base_eq_center j

theorem boundaryBase_eq_center_iff (D : BoundaryClusterData i a m S l u) (j : Fin m) :
    D.boundaryBase j = D.center ↔ j ∈ boundaryClusterBlock l u := by
  constructor
  · intro h
    by_contra hj
    have hj' : ¬(l.val ≤ j.val ∧ j.val < u.val) := by
      simpa only [mem_boundaryClusterBlock] using hj
    by_cases hleft : j.val < l.val
    · exact (D.boundaryBase_lt_center j hleft).ne h
    · have hright : u.val ≤ j.val := by omega
      exact (D.center_lt_boundaryBase j hright).ne' h
  · exact D.boundaryBase_eq_center j

theorem boundaryBase_eq_iff (D : BoundaryClusterData i a m S l u) (j k : Fin m) :
    D.boundaryBase j = D.boundaryBase k ↔
      j = k ∨ (j ∈ boundaryClusterBlock l u ∧ k ∈ boundaryClusterBlock l u) := by
  constructor
  · intro h
    by_cases hjk : j = k
    · exact Or.inl hjk
    · right
      by_contra hblock
      rcases lt_or_gt_of_ne hjk with hjk | hkj
      · exact (D.boundaryBase_lt j k hjk hblock).ne h
      · exact (D.boundaryBase_lt k j hkj (fun hk => hblock hk.symm)).ne h.symm
  · rintro (rfl | ⟨hj, hk⟩)
    · rfl
    · rw [D.boundaryBase_eq_center j hj, D.boundaryBase_eq_center k hk]

theorem doubledBase_eq_center_iff (D : BoundaryClusterData i a m S l u)
    (v : DoubledLabel n m) :
    D.doubledBase v = (D.center : ℂ) ↔ boundaryClusterCollapses S l u v := by
  cases v with
  | inl v =>
    cases v with
    | inl j => exact D.base_eq_center_iff j
    | inr j =>
      exact Complex.ofReal_injective.eq_iff.trans (D.boundaryBase_eq_center_iff j)
  | inr j =>
    change conj (D.base j) = (D.center : ℂ) ↔ j ∈ S
    rw [← Complex.conj_ofReal D.center]
    exact (starRingEnd ℂ).injective.eq_iff.trans (D.base_eq_center_iff j)

/-- Off the prescribed cluster, distinct doubled labels have distinct bases. -/
theorem doubledBase_injective_off (D : BoundaryClusterData i a m S l u)
    {v w : DoubledLabel n m} (hv : ¬boundaryClusterCollapses S l u v)
    (hw : ¬boundaryClusterCollapses S l u w) (h : D.doubledBase v = D.doubledBase w) : v = w := by
  rcases v with (v | v) | v <;> rcases w with (w | w) | w <;>
    simp only [boundaryClusterCollapses] at hv hw <;> simp only [doubledBase] at h
  · exact congrArg (fun j => Sum.inl (Sum.inl j)) (D.base_injective_off v w hv hw h)
  · have hi := congrArg Complex.im h
    simp only [Complex.ofReal_im] at hi
    exact False.elim ((D.base_im_pos_off v hv).ne' hi)
  · have hi := congrArg Complex.im h
    simp only [Complex.conj_im] at hi
    have hvp := D.base_im_pos_off v hv
    have hwp := D.base_im_pos_off w hw
    exfalso
    linarith
  · have hi := congrArg Complex.im h
    simp only [Complex.ofReal_im] at hi
    exact False.elim ((D.base_im_pos_off w hw).ne' hi.symm)
  · apply congrArg (fun j => Sum.inl (Sum.inr j))
    exact ((D.boundaryBase_eq_iff v w).mp (Complex.ofReal_injective h)).resolve_right
      (fun hblock => hv hblock.1)
  · have hi := congrArg Complex.im h
    simp only [Complex.ofReal_im, Complex.conj_im] at hi
    have hwp := D.base_im_pos_off w hw
    exfalso
    linarith
  · have hi := congrArg Complex.im h
    simp only [Complex.conj_im] at hi
    have hvp := D.base_im_pos_off v hv
    have hwp := D.base_im_pos_off w hw
    exfalso
    linarith
  · have hi := congrArg Complex.im h
    simp only [Complex.ofReal_im, Complex.conj_im] at hi
    have hvp := D.base_im_pos_off v hv
    exfalso
    linarith
  · exact congrArg Sum.inr (D.base_injective_off v w hv hw ((starRingEnd ℂ).injective h))

theorem doubledBase_eq_iff (D : BoundaryClusterData i a m S l u) (v w : DoubledLabel n m) :
    D.doubledBase v = D.doubledBase w ↔
      v = w ∨ (boundaryClusterCollapses S l u v ∧ boundaryClusterCollapses S l u w) := by
  constructor
  · intro h
    by_cases hv : boundaryClusterCollapses S l u v
    · right
      exact ⟨hv, (D.doubledBase_eq_center_iff w).mp
        (h.symm.trans ((D.doubledBase_eq_center_iff v).mpr hv))⟩
    · by_cases hw : boundaryClusterCollapses S l u w
      · exact False.elim (hv ((D.doubledBase_eq_center_iff v).mp
          (h.trans ((D.doubledBase_eq_center_iff w).mpr hw))))
      · exact Or.inl (D.doubledBase_injective_off hv hw h)
  · rintro (rfl | ⟨hv, hw⟩)
    · rfl
    · exact ((D.doubledBase_eq_center_iff v).mpr hv).trans
        ((D.doubledBase_eq_center_iff w).mpr hw).symm

theorem pairBase_eq_zero_iff_boundaryClusterPairCollapses (D : BoundaryClusterData i a m S l u)
    (p : DoubledPair n m) : D.pairBase p = 0 ↔ boundaryClusterPairCollapses S l u p := by
  rw [pairBase, sub_eq_zero, D.doubledBase_eq_iff]
  simp only [Ne.symm p.property, false_or, boundaryClusterPairCollapses, and_comm]

theorem pairVelocity_ne_zero_of_boundaryClusterPairCollapses (D : BoundaryClusterData i a m S l u)
    (p : DoubledPair n m) (hp : boundaryClusterPairCollapses S l u p) : D.pairVelocity p ≠ 0 :=
  D.pairVelocity_ne_zero_of_pairBase_eq_zero p
    ((D.pairBase_eq_zero_iff_boundaryClusterPairCollapses p).mpr hp)

end BoundaryClusterData

end EnvelopingIsomorphism.Deformation.Kontsevich
