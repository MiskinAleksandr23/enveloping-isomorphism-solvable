import EnvelopingIsomorphism.Deformation.GerstenhaberJacobi
import EnvelopingIsomorphism.Deformation.HochschildBracket

/-! Differential and bracket compatibility for positive-arity full Hochschild cochains. -/

namespace EnvelopingIsomorphism.Deformation

universe u v
variable {R : Type u} [CommRing R] {A : Type v} [AddCommGroup A] [Module R A]

def curriedDifferential (μ : Binary R A) (m : ℕ) :
    Curried R A (m + 1) →ₗ[R] Curried R A (m + 1 + 1) :=
  (-1 : R) ^ (m + 1 + 1) • curriedBar μ (m + 1)

theorem curriedDifferential_eq_bracket (μ : Binary R A) (m : ℕ)
    (f : Curried R A (m + 1)) :
    curriedDifferential μ m f =
      curriedCongr (Nat.add_comm 1 (m + 1)) (curriedBracket 1 m μ f) :=
  (curriedBracket_multiplication μ m f).symm

theorem curriedDifferential_sq (μ : Binary R A)
    (hμ : ∀ a b c, μ (μ a b) c = μ a (μ b c)) (m : ℕ) (f : Curried R A (m + 1)) :
    curriedDifferential μ (m + 1) (curriedDifferential μ m f) = 0 := by
  simp only [curriedDifferential, LinearMap.smul_apply, map_smul, curriedBar_sq μ hμ, smul_zero]

theorem curriedBracket_cast_outer {m m' n : ℕ} (hm : m + 1 = m' + 1)
    (f : Curried R A (m + 1)) (g : Curried R A (n + 1)) :
    curriedBracket m' n (curriedCongr hm f) g =
      curriedCongr (by omega : m + (n + 1) = m' + (n + 1)) (curriedBracket m n f g) := by
  have he := Nat.succ.inj hm
  subst m'
  rfl

theorem curriedBracket_cast_inner {m n n' : ℕ} (hn : n + 1 = n' + 1)
    (f : Curried R A (m + 1)) (g : Curried R A (n + 1)) :
    curriedBracket m n' f (curriedCongr hn g) =
      curriedCongr (congrArg (m + ·) hn) (curriedBracket m n f g) := by
  have he := Nat.succ.inj hn
  subst n'
  rfl

theorem curriedBracket_multiplication_raw (μ : Binary R A) (m : ℕ)
    (f : Curried R A (m + 1)) :
    curriedBracket 1 m μ f = curriedCongr (Nat.add_comm 1 (m + 1)).symm
      (curriedDifferential μ m f) := by
  rw [curriedDifferential_eq_bracket, curriedCongr_trans]
  rfl

/-- The full Hochschild differential is a graded derivation of the bracket.
No associativity is needed for the derivation identity itself. -/
theorem curriedDifferential_bracket (μ : Binary R A) (m n : ℕ)
    (f : Curried R A (m + 1)) (g : Curried R A (n + 1)) :
    curriedDifferential μ (m + n) (curriedBracket m n f g) =
      curriedCongr (by omega : (m + 1) + (n + 1) = (m + n) + 1 + 1)
        (curriedBracket (m + 1) n (curriedDifferential μ m f) g) +
      (-1 : R) ^ m • curriedBracket m (n + 1) f (curriedDifferential μ n g) := by
  have hj := curriedBracket_jacobi 1 m n μ f g
  have he := congrArg
    (curriedCongr (by omega : (1 + m) + (n + 1) = (m + n) + 1 + 1)) hj
  rw [map_add, map_smul, curriedCongr_trans,
    ← curriedDifferential_eq_bracket μ (m + n) (curriedBracket m n f g),
    curriedBracket_multiplication_raw μ m f, curriedBracket_multiplication_raw μ n g,
    curriedBracket_cast_outer, curriedBracket_cast_inner, curriedCongr_trans,
    curriedCongr_trans, Nat.one_mul] at he
  rw [curriedCongr_trans, curriedCongr_self] at he
  exact he

end EnvelopingIsomorphism.Deformation
