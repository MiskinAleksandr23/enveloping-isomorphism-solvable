import EnvelopingIsomorphism.Deformation.FullSymmetry

/-! The all-integer Hochschild differential is bracketing with multiplication. -/

namespace EnvelopingIsomorphism.Deformation

universe u v
variable {R : Type u} [CommRing R] {A : Type v} [AddCommGroup A] [Module R A]

theorem fullDifferential_eq_bracket (μ : Binary R A) (p : ℤ) (f : FullCochain R A p) :
    fullDifferential μ p f =
      fullCochainCongr (add_comm 1 p) (fullBracket 1 p μ f) := by
  cases p with
  | ofNat m =>
    have hc := fullCochainCongr_nat (R := R) (A := A)
      (congrArg Int.ofNat (Nat.add_comm 1 m)) (curriedBracket 1 m μ f)
    change curriedDifferential μ m f =
      fullCochainCongr (congrArg Int.ofNat (Nat.add_comm 1 m)) (curriedBracket 1 m μ f)
    rw [hc]
    exact curriedDifferential_eq_bracket μ m f
  | negSucc n =>
    cases n with
    | zero =>
      change differentialZero μ f = curriedPreLie 0 1 μ f
      exact (curriedPreLie_binary_constant μ f).symm
    | succ n =>
      rw [fullBracket_below_right 1 n μ f, map_zero]
      rfl

/-- The Leibniz defect of d is the corresponding Jacobi defect with multiplication. -/
theorem fullDifferential_bracket_defect (μ : Binary R A) (p q : ℤ)
    (f : FullCochain R A p) (g : FullCochain R A q) :
    fullDifferential μ (p + q) (fullBracket p q f g) -
      fullCochainCongr (by omega : (p + 1) + q = (p + q) + 1)
        (fullBracket (p + 1) q (fullDifferential μ p f) g) -
      koszulSign R p 1 • fullCochainCongr (add_assoc p q 1).symm
        (fullBracket p (q + 1) f (fullDifferential μ q g)) =
      fullCochainCongr (by omega : (1 + p) + q = (p + q) + 1)
        (fullJacobiator 1 p q μ f g) := by
  rw [fullDifferential_eq_bracket μ (p + q) (fullBracket p q f g),
    fullDifferential_eq_bracket μ p f, fullDifferential_eq_bracket μ q g,
    fullBracket_cast_left, fullBracket_cast_right]
  simp only [fullJacobiator, map_sub, map_smul]
  repeat' first
    | rw [fullCochainCongr_trans]
    | rw [fullCochainCongr_self]
  rw [koszulSign_comm p 1]

end EnvelopingIsomorphism.Deformation
