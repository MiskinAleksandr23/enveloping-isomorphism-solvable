import EnvelopingIsomorphism.Deformation.FullJacobi

/-! Integer Koszul signs and transport-compatible symmetries of the full bracket. -/

namespace EnvelopingIsomorphism.Deformation

universe u v
variable {R : Type u} [CommRing R] {A : Type v} [AddCommGroup A] [Module R A]

theorem koszulSign_add_left (p q r : ℤ) :
    koszulSign R (p + q) r = koszulSign R p r * koszulSign R q r := by
  unfold koszulSign
  rw [add_mul, Int.negOnePow_add]
  simp only [Units.val_mul, Int.cast_mul]

theorem koszulSign_add_right (p q r : ℤ) :
    koszulSign R p (q + r) = koszulSign R p q * koszulSign R p r := by
  rw [koszulSign_comm, koszulSign_add_left, koszulSign_comm q p, koszulSign_comm r p]

theorem koszulSign_square (p q : ℤ) : koszulSign R p q * koszulSign R p q = 1 := by
  have hu := Int.units_mul_self (p * q).negOnePow
  simpa only [koszulSign, Units.val_mul, Int.cast_mul, Units.val_one, Int.cast_one] using
    congrArg (fun z : ℤˣ => ((z : ℤ) : R)) hu

theorem fullBracket_cast_left {p p' q : ℤ} (hp : p = p')
    (f : FullCochain R A p) (g : FullCochain R A q) :
    fullBracket p' q (fullCochainCongr hp f) g =
      fullCochainCongr (congrArg (· + q) hp) (fullBracket p q f g) := by
  subst p'
  rfl

theorem fullBracket_cast_right {p q q' : ℤ} (hq : q = q')
    (f : FullCochain R A p) (g : FullCochain R A q) :
    fullBracket p q' f (fullCochainCongr hq g) =
      fullCochainCongr (congrArg (p + ·) hq) (fullBracket p q f g) := by
  subst q'
  rfl

theorem fullBracket_skew_eq (p q : ℤ) (f : FullCochain R A p) (g : FullCochain R A q) :
    fullBracket p q f g = -koszulSign R p q •
      fullCochainCongr (add_comm q p) (fullBracket q p g f) := by
  exact eq_of_heq ((fullBracket_skew p q f g).trans
    (fullCochainCongr_smul_heq (add_comm q p) (-koszulSign R p q) (fullBracket q p g f)).symm)

end EnvelopingIsomorphism.Deformation
