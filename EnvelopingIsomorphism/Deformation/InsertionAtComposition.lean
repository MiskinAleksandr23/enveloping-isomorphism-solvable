import EnvelopingIsomorphism.Deformation.InsertionComposition
import EnvelopingIsomorphism.Deformation.InsertionSum

/-! Finite-slot versions of the actual insertion composition laws. -/

namespace EnvelopingIsomorphism.Deformation

universe u v
variable {R : Type u} [CommRing R] {A : Type v} [AddCommGroup A] [Module R A]

/-- Finite-slot insertion agrees with the prefix/suffix recursive insertion. -/
theorem curriedInsertAt_prefix (p q r : ℕ)
    (f : Curried R A ((q + 1) + p)) (g : Curried R A r) :
    curriedCongr (by omega : (q + p) + r = (q + r) + p)
      (curriedInsertAt (q + p) r ⟨p, by omega⟩
        (curriedCongr (by omega : (q + 1) + p = (q + p) + 1) f) g) =
      curriedInsert q r p f g := by
  induction p with
  | zero =>
      convert curriedInsertAt_zero q r f g using 1 <;> rfl
  | succ p ih =>
      change curriedCongr _
        (curriedInsertAt ((q + p) + 1) r (⟨p, by omega⟩ : Fin ((q + p) + 1)).succ
          (curriedCongr _ f) g) = _
      rw [curriedInsertAt_succ_eq, curriedCongr_trans]
      apply LinearMap.ext
      intro a
      have houter := curriedCongr_apply
        (m := (q + p) + r) (n := (q + r) + p) (by omega)
        (curriedLiftPrefix (curriedInsertAt (q + p) r ⟨p, by omega⟩)
          (curriedCongr (by omega) f) g) a
      have hinner := curriedCongr_apply
        (m := (q + 1) + p) (n := (q + p) + 1) (by omega) f a
      exact houter.trans ((congrArg
        (fun F : Curried R A ((q + p) + 1) ↦
          curriedCongr (by omega : (q + p) + r = (q + r) + p)
            (curriedInsertAt (q + p) r ⟨p, by omega⟩ F g)) hinner).trans (ih (f a)))

/-- The prefix bridge with independent but equal arity expressions. This lemma
keeps the final slot identities free of accidental choices of arithmetic casts. -/
theorem curriedInsertAt_heq_insert {m n p q r : ℕ} (hm : m = q + p) (hn : n = r)
    (i : Fin (m + 1)) (hi : (i : ℕ) = p)
    (f : Curried R A (m + 1)) (F : Curried R A ((q + 1) + p)) (hf : HEq f F)
    (g : Curried R A n) (G : Curried R A r) (hg : HEq g G) :
    HEq (curriedInsertAt m n i f g) (curriedInsert q r p F G) := by
  subst n
  have hgeq : g = G := eq_of_heq hg
  subst g
  subst m
  have hi' : i = ⟨p, by omega⟩ := Fin.ext hi
  rw [hi']
  have hF : curriedCongr (by omega : (q + 1) + p = (q + p) + 1) F = f :=
    eq_of_heq ((curriedCongr_heq _ F).trans hf.symm)
  have hbridge := curriedInsertAt_prefix p q r F G
  rw [hF] at hbridge
  exact (curriedCongr_heq (by omega : (q + p) + r = (q + r) + p)
    (curriedInsertAt (q + p) r ⟨p, by omega⟩ f G)).symm.trans (heq_of_eq hbridge)

/-- Nested insertion law with genuine finite slot indices. The innermost arity t
may be zero; the other two operations have the slots explicitly selected by i and j. -/
theorem curriedInsertAt_nested (m n t : ℕ) (i : Fin (m + 1)) (j : Fin (n + 1))
    (f : Curried R A (m + 1)) (g : Curried R A (n + 1)) (h : Curried R A t) :
    curriedCongr (Nat.add_assoc m n t)
      (curriedInsertAt (m + n) t ⟨(i : ℕ) + (j : ℕ), by omega⟩
        (curriedInsertAt m (n + 1) i f g) h) =
      curriedInsertAt m (n + t) i f (curriedInsertAt n t j g h) := by
  let p : ℕ := i
  let r : ℕ := j
  let q := m - p
  let s := n - r
  have hm : m = q + p := by dsimp [q, p]; omega
  have hn : n = s + r := by dsimp [s, r]; omega
  let F : Curried R A ((q + 1) + p) := curriedCongr (by omega) f
  let G : Curried R A ((s + 1) + r) := curriedCongr (by omega) g
  have hf : HEq f F := (curriedCongr_heq _ f).symm
  have hg : HEq g G := (curriedCongr_heq _ g).symm
  have hfirst := curriedInsertAt_heq_insert hm (by omega : n + 1 = (s + 1) + r)
    i rfl f F hf g G hg
  let F₁ : Curried R A (((q + s) + 1) + (r + p)) :=
    curriedCongr (by omega) (curriedInsert q ((s + 1) + r) p F G)
  have hf₁ : HEq (curriedInsertAt m (n + 1) i f g) F₁ :=
    hfirst.trans (curriedCongr_heq _ _).symm
  have hsecond := curriedInsertAt_heq_insert
    (by omega : m + n = (q + s) + (r + p)) (rfl : t = t)
    (⟨(i : ℕ) + (j : ℕ), by omega⟩ : Fin ((m + n) + 1))
    (by dsimp [p, r]; omega) (curriedInsertAt m (n + 1) i f g) F₁ hf₁ h h HEq.rfl
  have hinner := curriedInsertAt_heq_insert hn rfl j rfl g G hg h h HEq.rfl
  have hright := curriedInsertAt_heq_insert hm
    (by omega : n + t = (s + t) + r) i rfl f F hf
    (curriedInsertAt n t j g h) (curriedInsert s t r G h) hinner
  have hnested : HEq (curriedInsert (q + s) t (r + p) F₁ h)
      (curriedInsert q ((s + t) + r) p F (curriedInsert s t r G h)) :=
    (curriedCongr_heq (by omega : ((q + s) + t) + (r + p) = (q + ((s + t) + r)) + p)
      (curriedInsert (q + s) t (r + p) F₁ h)).symm.trans
        (heq_of_eq (curriedInsert_nested p q r s t F G h))
  exact eq_of_heq ((curriedCongr_heq (Nat.add_assoc m n t) _).trans
    (hsecond.trans (hnested.trans hright.symm)))

/-- Disjoint insertion law for two finite slots i < j. Both inserted arities may
be zero. The later slot becomes `j + n - 1` after the n-ary insertion at i. -/
theorem curriedInsertAt_disjoint (m n r : ℕ) (i j : Fin ((m + 1) + 1)) (hij : i < j)
    (f : Curried R A ((m + 1) + 1)) (g : Curried R A n) (h : Curried R A r) :
    curriedCongr (Nat.add_right_comm m n r)
      (curriedInsertAt (m + n) r ⟨(j : ℕ) + n - 1, by omega⟩
        (curriedCongr (Nat.add_right_comm m 1 n) (curriedInsertAt (m + 1) n i f g)) h) =
      curriedInsertAt (m + r) n ⟨(i : ℕ), by omega⟩
        (curriedCongr (Nat.add_right_comm m 1 r) (curriedInsertAt (m + 1) r j f h)) g := by
  let p : ℕ := i
  let q : ℕ := (j : ℕ) - p - 1
  let s : ℕ := m + 1 - (j : ℕ)
  have hcount : m = (s + q) + p := by dsimp [p, q, s]; omega
  have hj : (j : ℕ) = (q + 1) + p := by dsimp [p, q]; omega
  let F : Curried R A ((((s + 1) + q) + 1) + p) := curriedCongr (by omega) f
  have hf : HEq f F := (curriedCongr_heq _ f).symm
  have hfirst := curriedInsertAt_heq_insert
    (by omega : m + 1 = ((s + 1) + q) + p) rfl i rfl f F hf g g HEq.rfl
  let F₁ : Curried R A ((s + 1) + ((q + n) + p)) :=
    curriedCongr (by omega) (curriedInsert ((s + 1) + q) n p F g)
  have hf₁ : HEq
      (curriedCongr (Nat.add_right_comm m 1 n) (curriedInsertAt (m + 1) n i f g)) F₁ :=
    (curriedCongr_heq _ _).trans (hfirst.trans (curriedCongr_heq _ _).symm)
  have hsecond := curriedInsertAt_heq_insert
    (by omega : m + n = s + ((q + n) + p)) (rfl : r = r)
    (⟨(j : ℕ) + n - 1, by omega⟩ : Fin ((m + n) + 1))
    (by change (j : ℕ) + n - 1 = (q + n) + p; omega)
    (curriedCongr (Nat.add_right_comm m 1 n) (curriedInsertAt (m + 1) n i f g))
    F₁ hf₁ h h HEq.rfl
  let F₀ : Curried R A ((s + 1) + ((q + 1) + p)) := curriedCongr (by omega) F
  have hf₀ : HEq f F₀ := hf.trans (curriedCongr_heq _ F).symm
  have hreverse := curriedInsertAt_heq_insert
    (by omega : m + 1 = s + ((q + 1) + p)) (rfl : r = r)
    j hj f F₀ hf₀ h h HEq.rfl
  let F₂ : Curried R A ((((s + r) + q) + 1) + p) :=
    curriedCongr (by omega) (curriedInsert s r ((q + 1) + p) F₀ h)
  have hf₂ : HEq
      (curriedCongr (Nat.add_right_comm m 1 r) (curriedInsertAt (m + 1) r j f h)) F₂ :=
    (curriedCongr_heq _ _).trans (hreverse.trans (curriedCongr_heq _ _).symm)
  have hright := curriedInsertAt_heq_insert
    (by omega : m + r = ((s + r) + q) + p) (rfl : n = n)
    (⟨(i : ℕ), by omega⟩ : Fin ((m + r) + 1)) rfl
    (curriedCongr (Nat.add_right_comm m 1 r) (curriedInsertAt (m + 1) r j f h))
    F₂ hf₂ g g HEq.rfl
  have hdisjoint : HEq (curriedInsert s r ((q + n) + p) F₁ h)
      (curriedInsert ((s + r) + q) n p F₂ g) :=
    (curriedCongr_heq
      (by omega : (s + r) + ((q + n) + p) = (((s + r) + q) + n) + p)
      (curriedInsert s r ((q + n) + p) F₁ h)).symm.trans
        (heq_of_eq (curriedInsert_disjoint p q s n r F g h))
  exact eq_of_heq ((curriedCongr_heq (Nat.add_right_comm m n r) _).trans
    (hsecond.trans (hdisjoint.trans hright.symm)))

/-- Equivalent finite-slot law when the second insertion is before the first.
This retains both constant-arity cases explicitly through natural-number slot subtraction. -/
theorem curriedInsertAt_before (m n r : ℕ) (i j : Fin ((m + 1) + 1)) (hji : j < i)
    (f : Curried R A ((m + 1) + 1)) (g : Curried R A n) (h : Curried R A r) :
    curriedCongr (Nat.add_right_comm m n r)
      (curriedInsertAt (m + n) r ⟨(j : ℕ), by omega⟩
        (curriedCongr (Nat.add_right_comm m 1 n) (curriedInsertAt (m + 1) n i f g)) h) =
      curriedInsertAt (m + r) n ⟨(i : ℕ) + r - 1, by omega⟩
        (curriedCongr (Nat.add_right_comm m 1 r) (curriedInsertAt (m + 1) r j f h)) g := by
  have hdisjoint := curriedInsertAt_disjoint m r n j i hji f h g
  have heq := congrArg (curriedCongr (Nat.add_right_comm m n r)) hdisjoint.symm
  simpa only [curriedCongr_trans, curriedCongr_rfl] using heq

end EnvelopingIsomorphism.Deformation
