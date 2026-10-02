import EnvelopingIsomorphism.Deformation.Kontsevich.InteriorCluster

/-! The vanishing pair-base pattern of one interior cluster depends only on
the cluster labels. It does not depend on varying base points or velocities. -/

namespace EnvelopingIsomorphism.Deformation.Kontsevich

open Configuration ComplexConjugate
open scoped UpperHalfPlane

/-- A pair collapses exactly when both labels lie in the original interior
cluster, or both lie in its conjugate copy. Boundary and cross-type pairs do not collapse. -/
def clusterPairCollapses {n m : ℕ} (S : Finset (Fin n)) (p : DoubledPair n m) : Prop :=
  match p.val.1, p.val.2 with
  | Sum.inl (Sum.inl a), Sum.inl (Sum.inl b) => a ∈ S ∧ b ∈ S
  | Sum.inr a, Sum.inr b => a ∈ S ∧ b ∈ S
  | _, _ => False

instance {n m : ℕ} (S : Finset (Fin n)) (p : DoubledPair n m) :
    Decidable (clusterPairCollapses S p) := by
  unfold clusterPairCollapses
  split <;> infer_instance

private theorem upper_ne_real (z : ℍ) (r : ℝ) : (z : ℂ) ≠ (r : ℂ) := by
  intro h
  have hi := congrArg Complex.im h
  simp only [UpperHalfPlane.coe_im, Complex.ofReal_im] at hi
  exact z.im_pos.ne' hi

private theorem upper_ne_conjugate (z w : ℍ) : (z : ℂ) ≠ conj (w : ℂ) := by
  intro h
  have hi := congrArg Complex.im h
  simp only [UpperHalfPlane.coe_im, Complex.conj_im] at hi
  have hz := z.im_pos
  have hw := w.im_pos
  linarith

private theorem real_ne_conjugate (r : ℝ) (z : ℍ) : (r : ℂ) ≠ conj (z : ℂ) := by
  intro h
  have hi := congrArg Complex.im h
  simp only [Complex.ofReal_im, Complex.conj_im, UpperHalfPlane.coe_im] at hi
  have hz := z.im_pos
  linarith

namespace SingleInteriorCluster

variable {n m : ℕ} {i : Fin n} {S : Finset (Fin n)}

private theorem coe_base_eq_iff_cluster_mem (D : SingleInteriorCluster i m S)
    {a b : Fin n} (hab : a ≠ b) :
    (D.base a : ℂ) = (D.base b : ℂ) ↔ a ∈ S ∧ b ∈ S := by
  constructor
  · intro h
    exact ((D.base_eq_iff a b).mp (UpperHalfPlane.ext h)).resolve_left hab
  · intro h
    exact congrArg (fun z : ℍ => (z : ℂ)) (D.base_eq_of_mem h.1 h.2)

/-- The zero-base-difference test is exactly the fixed combinatorial cluster mask. -/
theorem pairBase_eq_zero_iff_clusterPairCollapses (D : SingleInteriorCluster i m S)
    (p : DoubledPair n m) :
    D.toInteriorCollisionData.pairBase p = 0 ↔ clusterPairCollapses S p := by
  rcases p with ⟨⟨u, v⟩, huv⟩
  cases u with
  | inl u =>
    cases u with
    | inl a =>
      cases v with
      | inl v =>
        cases v with
        | inl b =>
          have hab : b ≠ a := by intro h; subst b; exact huv rfl
          simpa only [InteriorCollisionData.pairBase, InteriorCollisionData.doubledBase,
            clusterPairCollapses, sub_eq_zero, and_comm] using D.coe_base_eq_iff_cluster_mem hab
        | inr b =>
          simp only [InteriorCollisionData.pairBase, InteriorCollisionData.doubledBase,
            clusterPairCollapses, sub_eq_zero]
          exact iff_false_intro (upper_ne_real (D.base a) (D.boundary b)).symm
      | inr b =>
        simp only [InteriorCollisionData.pairBase, InteriorCollisionData.doubledBase,
          clusterPairCollapses, sub_eq_zero]
        exact iff_false_intro (upper_ne_conjugate (D.base a) (D.base b)).symm
    | inr a =>
      cases v with
      | inl v =>
        cases v with
        | inl b =>
          simp only [InteriorCollisionData.pairBase, InteriorCollisionData.doubledBase,
            clusterPairCollapses, sub_eq_zero]
          exact iff_false_intro (upper_ne_real (D.base b) (D.boundary a))
        | inr b =>
          simp only [InteriorCollisionData.pairBase, InteriorCollisionData.doubledBase,
            clusterPairCollapses, sub_eq_zero]
          apply iff_false_intro
          intro h
          have hab := D.boundary_strictMono.injective (Complex.ofReal_injective h)
          subst b
          exact huv rfl
      | inr b =>
        simp only [InteriorCollisionData.pairBase, InteriorCollisionData.doubledBase,
          clusterPairCollapses, sub_eq_zero]
        exact iff_false_intro (real_ne_conjugate (D.boundary a) (D.base b)).symm
  | inr a =>
    cases v with
    | inl v =>
      cases v with
      | inl b =>
        simp only [InteriorCollisionData.pairBase, InteriorCollisionData.doubledBase,
          clusterPairCollapses, sub_eq_zero]
        exact iff_false_intro (upper_ne_conjugate (D.base b) (D.base a))
      | inr b =>
        simp only [InteriorCollisionData.pairBase, InteriorCollisionData.doubledBase,
          clusterPairCollapses, sub_eq_zero]
        exact iff_false_intro (real_ne_conjugate (D.boundary b) (D.base a))
    | inr b =>
      have hab : b ≠ a := by intro h; subst b; exact huv rfl
      simp only [InteriorCollisionData.pairBase, InteriorCollisionData.doubledBase,
        clusterPairCollapses, sub_eq_zero]
      exact (starRingEnd ℂ).injective.eq_iff.trans
        ((D.coe_base_eq_iff_cluster_mem hab).trans and_comm)

/-- A pair selected by the fixed collapse mask has a nonzero first-order velocity. -/
theorem pairVelocity_ne_zero_of_clusterPairCollapses (D : SingleInteriorCluster i m S)
    (p : DoubledPair n m) (hp : clusterPairCollapses S p) :
    D.toInteriorCollisionData.pairVelocity p ≠ 0 :=
  D.toInteriorCollisionData.pairVelocity_ne_zero_of_pairBase_eq_zero p
    ((D.pairBase_eq_zero_iff_clusterPairCollapses p).mpr hp)

end SingleInteriorCluster
end EnvelopingIsomorphism.Deformation.Kontsevich
