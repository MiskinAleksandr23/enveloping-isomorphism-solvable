import EnvelopingIsomorphism.Deformation.FullAssociatorConstants
import EnvelopingIsomorphism.Deformation.FullJacobiExpansion
import EnvelopingIsomorphism.Deformation.FullDifferentialBracket
import EnvelopingIsomorphism.Deformation.SignedDGLA

/-!
The genuine signed DGLA of all Hochschild cochains.  All integer degrees,
including degree -1, are included.  Its Jacobi law is proved from the actual
insertion operations, with separate constant-arity boundary calculations.
-/

namespace EnvelopingIsomorphism.Deformation

universe u v
variable {R : Type u} [CommRing R] {A : Type v} [AddCommGroup A] [Module R A]

theorem fullAssociator_graded_symm (p q r : ℤ) (f : FullCochain R A p)
    (g : FullCochain R A q) (h : FullCochain R A r) :
    fullAssociator p q r f g h = koszulSign R q r •
      fullCochainCongr (by omega : (p + r) + q = (p + q) + r)
        (fullAssociator p r q f h g) := by
  cases p with
  | negSucc m =>
    rw [fullAssociator_neg_outer m q r f g h, fullAssociator_neg_outer m r q f h g,
      map_zero, smul_zero]
  | ofNat m =>
    cases q with
    | ofNat n =>
      cases r with
      | ofNat l => exact fullAssociator_nat_symm m n l f g h
      | negSucc l =>
        cases l with
        | zero => exact fullAssociator_nat_nat_constant_symm m n f g h
        | succ l =>
          rw [fullAssociator_below_third _ _ l f g h,
            fullAssociator_below_second _ l _ f h g, map_zero, smul_zero]
    | negSucc n =>
      cases n with
      | zero =>
        cases r with
        | ofNat l => exact fullAssociator_nat_constant_nat_symm m l f g h
        | negSucc l =>
          cases l with
          | zero => exact fullAssociator_nat_constants_symm m f g h
          | succ l =>
            rw [fullAssociator_below_third _ _ l f g h,
              fullAssociator_below_second _ l _ f h g, map_zero, smul_zero]
      | succ n =>
        rw [fullAssociator_below_second _ n _ f g h,
          fullAssociator_below_third _ _ n f h g, map_zero, smul_zero]

/-- Jacobi holds in every integer degree of the full Hochschild complex. -/
theorem fullJacobiator_zero (p q r : ℤ) (f : FullCochain R A p)
    (g : FullCochain R A q) (h : FullCochain R A r) : fullJacobiator p q r f g h = 0 := by
  rw [fullJacobiator_eq_associators]
  have h₁ := sub_eq_zero.mpr (fullAssociator_graded_symm p q r f g h)
  have h₂ := sub_eq_zero.mpr (fullAssociator_graded_symm q p r g f h)
  have h₃ := sub_eq_zero.mpr (fullAssociator_graded_symm r p q h f g)
  rw [h₁, h₂, h₃]
  simp only [neg_zero, map_zero, smul_zero, add_zero, sub_zero]

theorem fullBracket_jacobi (p q r : ℤ) (f : FullCochain R A p)
    (g : FullCochain R A q) (h : FullCochain R A r) :
    fullCochainCongr (add_assoc p q r).symm (fullBracket p (q + r) f (fullBracket q r g h)) =
      fullBracket (p + q) r (fullBracket p q f g) h +
        koszulSign R p q • fullCochainCongr (by omega : q + (p + r) = (p + q) + r)
          (fullBracket q (p + r) g (fullBracket p r f h)) := by
  have hj := fullJacobiator_zero p q r f g h
  change _ - _ - _ = 0 at hj
  rw [sub_sub] at hj
  exact sub_eq_zero.mp hj

theorem fullDifferential_bracket (μ : Binary R A) (p q : ℤ)
    (f : FullCochain R A p) (g : FullCochain R A q) :
    fullDifferential μ (p + q) (fullBracket p q f g) =
      fullCochainCongr (by omega : (p + 1) + q = (p + q) + 1)
        (fullBracket (p + 1) q (fullDifferential μ p f) g) +
      koszulSign R p 1 • fullCochainCongr (add_assoc p q 1).symm
        (fullBracket p (q + 1) f (fullDifferential μ q g)) := by
  have hd := fullDifferential_bracket_defect μ p q f g
  rw [fullJacobiator_zero, map_zero, sub_sub] at hd
  exact sub_eq_zero.mp hd

@[simp] theorem fullComplex_d (μ : Binary R A)
    (hμ : ∀ a b c, μ (μ a b) c = μ a (μ b c)) (p : ℤ) :
    ((fullComplex μ hμ).d p (p + 1)).hom = fullDifferential μ p := by
  simp only [fullComplex, CochainComplex.of_d]
  rfl

/-- The full Hochschild cochains of any associative bilinear product form a signed DGLA. -/
def hochschildDGLA (μ : Binary R A) (hμ : ∀ a b c, μ (μ a b) c = μ a (μ b c)) :
    SignedDGLA.{u, v} R where
  complex := fullComplex μ hμ
  bracket := fullBracket
  skew := fullBracket_skew
  jacobi := fullBracket_jacobi
  differential_bracket p q f g := by
    simp only [fullComplex_d]
    change fullDifferential μ (p + q) (fullBracket p q f g) =
      fullCochainCongr (by omega : (p + 1) + q = (p + q) + 1)
        (fullBracket (p + 1) q (fullDifferential μ p f) g) +
      (p.negOnePow : R) • fullCochainCongr (add_assoc p q 1).symm
        (fullBracket p (q + 1) f (fullDifferential μ q g))
    simpa only [koszulSign, mul_one] using fullDifferential_bracket μ p q f g

end EnvelopingIsomorphism.Deformation
