import EnvelopingIsomorphism.Deformation.Insertion

/-!
Operadic composition laws for the actual recursive insertions of full cochains.
All inner arities are arbitrary natural numbers, so insertion of constants is
included. Arity transports only express associativity of finite slot counts.
-/

namespace EnvelopingIsomorphism.Deformation

universe u v
variable {R : Type u} [CommRing R] {A : Type v} [AddCommGroup A] [Module R A]

/-- An arity transport preserves the underlying heterogeneous cochain value. -/
theorem curriedCongr_heq {m n : ℕ} (h : m = n) (f : Curried R A m) :
    HEq (curriedCongr h f) f := by
  subst n
  rfl

/-- Arity transport of a curried cochain commutes with evaluating its first argument. -/
theorem curriedCongr_apply {m n : ℕ} (h : m + 1 = n + 1)
    (f : Curried R A (m + 1)) (a : A) :
    curriedCongr h f a = curriedCongr (Nat.succ.inj h) (f a) :=
  curriedCongr_succ (Nat.succ.inj h) f a

/-- Associativity of nested insertions into the first slot, including a constant innermost cochain. -/
theorem curriedInsertHead_nested (q r s : ℕ) (f : Curried R A (q + 1))
    (g : Curried R A (r + 1)) (h : Curried R A s) :
    curriedCongr (Nat.add_assoc q r s)
      (curriedInsertHead (q + r) s (curriedInsertHead q (r + 1) f g) h) =
      curriedInsertHead q (r + s) f (curriedInsertHead r s g h) := by
  induction s with
  | zero => rfl
  | succ s ih =>
    apply LinearMap.ext
    intro a
    exact (curriedCongr_apply (Nat.add_assoc q r (s + 1))
      (curriedInsertHead (q + r) (s + 1) (curriedInsertHead q (r + 1) f g) h) a).trans
        (ih (h a))

/-- A first-slot insertion followed by insertion in an arbitrary slot of the
inserted cochain agrees with the corresponding nested insertion. -/
theorem curriedInsertHead_nested_prefix (q r s t : ℕ)
    (f : Curried R A (q + 1)) (g : Curried R A ((s + 1) + r)) (h : Curried R A t) :
    curriedCongr (by omega : ((q + s) + t) + r = q + ((s + t) + r))
      (curriedInsert (q + s) t r
        (curriedCongr (by omega : q + ((s + 1) + r) = ((q + s) + 1) + r)
          (curriedInsertHead q ((s + 1) + r) f g)) h) =
      curriedInsertHead q ((s + t) + r) f (curriedInsert s t r g h) := by
  induction r with
  | zero =>
      convert curriedInsertHead_nested q s t f g h using 1 <;> rfl
  | succ r ih =>
      apply LinearMap.ext
      intro a
      have houter := curriedCongr_apply
        (m := ((q + s) + t) + r) (n := q + ((s + t) + r))
        (by omega)
        (curriedInsert (q + s) t (r + 1)
          (curriedCongr (by omega) (curriedInsertHead q ((s + 1) + (r + 1)) f g)) h) a
      have hinner := curriedCongr_apply
        (m := q + ((s + 1) + r)) (n := ((q + s) + 1) + r)
        (by omega) (curriedInsertHead q ((s + 1) + (r + 1)) f g) a
      exact houter.trans ((congrArg
        (fun F : Curried R A (((q + s) + 1) + r) ↦
          curriedCongr (by omega : ((q + s) + t) + r = q + ((s + t) + r))
            (curriedInsert (q + s) t r F h)) hinner).trans (ih (g a)))

/-- Nested insertion law at arbitrary outer and inner slots.
The combined slot has prefix `r + p` and suffix `q + s`. -/
theorem curriedInsert_nested (p q r s t : ℕ)
    (f : Curried R A ((q + 1) + p)) (g : Curried R A ((s + 1) + r))
    (h : Curried R A t) :
    curriedCongr (by omega : ((q + s) + t) + (r + p) = (q + ((s + t) + r)) + p)
      (curriedInsert (q + s) t (r + p)
        (curriedCongr (by omega : (q + ((s + 1) + r)) + p = ((q + s) + 1) + (r + p))
          (curriedInsert q ((s + 1) + r) p f g)) h) =
      curriedInsert q ((s + t) + r) p f (curriedInsert s t r g h) := by
  induction p with
  | zero =>
      simpa only [Nat.add_zero, curriedInsert_zero] using
        curriedInsertHead_nested_prefix q r s t f g h
  | succ p ih =>
      apply LinearMap.ext
      intro a
      have houter := curriedCongr_apply
        (m := ((q + s) + t) + (r + p)) (n := (q + ((s + t) + r)) + p)
        (by omega)
        (curriedInsert (q + s) t (r + (p + 1))
          (curriedCongr (by omega) (curriedInsert q ((s + 1) + r) (p + 1) f g)) h) a
      have hinner := curriedCongr_apply
        (m := (q + ((s + 1) + r)) + p) (n := ((q + s) + 1) + (r + p))
        (by omega) (curriedInsert q ((s + 1) + r) (p + 1) f g) a
      exact houter.trans ((congrArg
        (fun F : Curried R A (((q + s) + 1) + (r + p)) ↦
          curriedCongr (by omega : ((q + s) + t) + (r + p) = (q + ((s + t) + r)) + p)
            (curriedInsert (q + s) t (r + p) F h)) hinner).trans (ih (f a)))

/-- Insertion into the first slot commutes with insertion into a later outer slot.
There are `q` unchanged slots between them; either inserted cochain may be constant. -/
theorem curriedInsertHead_disjoint (q r m n : ℕ)
    (f : Curried R A (((r + 1) + q) + 1)) (g : Curried R A m) (h : Curried R A n) :
    curriedCongr (Nat.add_assoc (r + n) q m).symm
      (curriedInsert r n (q + m)
        (curriedCongr (Nat.add_assoc (r + 1) q m)
          (curriedInsertHead ((r + 1) + q) m f g)) h) =
      curriedInsertHead ((r + n) + q) m (curriedInsert r n (q + 1) f h) g := by
  induction m with
  | zero => rfl
  | succ m ih =>
      apply LinearMap.ext
      intro a
      have houter := curriedCongr_apply
        (m := (r + n) + (q + m)) (n := ((r + n) + q) + m)
        (by omega)
        (curriedInsert r n (q + (m + 1))
          (curriedCongr (Nat.add_assoc (r + 1) q (m + 1))
            (curriedInsertHead ((r + 1) + q) (m + 1) f g)) h) a
      have hinner := curriedCongr_apply
        (m := ((r + 1) + q) + m) (n := (r + 1) + (q + m))
        (Nat.add_assoc (r + 1) q (m + 1))
        (curriedInsertHead ((r + 1) + q) (m + 1) f g) a
      exact houter.trans ((congrArg
        (fun F : Curried R A ((r + 1) + (q + m)) ↦
          curriedCongr (Nat.add_assoc (r + n) q m).symm (curriedInsert r n (q + m) F h))
        hinner).trans (ih (g a)))

/-- Disjoint insertions commute. The original outer cochain has a prefix of
length p, then the first slot, q intervening slots, the second slot and r suffix slots. -/
theorem curriedInsert_disjoint (p q r m n : ℕ)
    (f : Curried R A ((((r + 1) + q) + 1) + p))
    (g : Curried R A m) (h : Curried R A n) :
    curriedCongr (by omega : (r + n) + ((q + m) + p) = (((r + n) + q) + m) + p)
      (curriedInsert r n ((q + m) + p)
        (curriedCongr (by omega : (((r + 1) + q) + m) + p = (r + 1) + ((q + m) + p))
          (curriedInsert ((r + 1) + q) m p f g)) h) =
      curriedInsert ((r + n) + q) m p
        (curriedCongr (by omega : (r + n) + ((q + 1) + p) = (((r + n) + q) + 1) + p)
          (curriedInsert r n ((q + 1) + p)
            (curriedCongr (by omega : (((r + 1) + q) + 1) + p = (r + 1) + ((q + 1) + p)) f)
            h)) g := by
  induction p with
  | zero =>
      convert curriedInsertHead_disjoint q r m n f g h using 1 <;> rfl
  | succ p ih =>
      apply LinearMap.ext
      intro a
      have houter := curriedCongr_apply
        (m := (r + n) + ((q + m) + p)) (n := (((r + n) + q) + m) + p)
        (by omega)
        (curriedInsert r n ((q + m) + (p + 1))
          (curriedCongr (by omega) (curriedInsert ((r + 1) + q) m (p + 1) f g)) h) a
      have hinner := curriedCongr_apply
        (m := (((r + 1) + q) + m) + p) (n := (r + 1) + ((q + m) + p))
        (by omega) (curriedInsert ((r + 1) + q) m (p + 1) f g) a
      have hleft := houter.trans (congrArg
        (fun F : Curried R A ((r + 1) + ((q + m) + p)) ↦
          curriedCongr (by omega : (r + n) + ((q + m) + p) = (((r + n) + q) + m) + p)
            (curriedInsert r n ((q + m) + p) F h)) hinner)
      have hreverseOuter := curriedCongr_apply
        (m := (r + n) + ((q + 1) + p)) (n := (((r + n) + q) + 1) + p)
        (by omega)
        (curriedInsert r n ((q + 1) + (p + 1))
          (curriedCongr (by omega) f) h) a
      have hreverseInner := curriedCongr_apply
        (m := (((r + 1) + q) + 1) + p) (n := (r + 1) + ((q + 1) + p))
        (by omega) f a
      have hreverse := hreverseOuter.trans (congrArg
        (fun F : Curried R A ((r + 1) + ((q + 1) + p)) ↦
          curriedCongr (by omega : (r + n) + ((q + 1) + p) = (((r + n) + q) + 1) + p)
            (curriedInsert r n ((q + 1) + p) F h)) hreverseInner)
      have hright := congrArg
        (fun F : Curried R A ((((r + n) + q) + 1) + p) ↦
          curriedInsert ((r + n) + q) m p F g) hreverse
      exact hleft.trans ((ih (f a)).trans hright.symm)

end EnvelopingIsomorphism.Deformation
