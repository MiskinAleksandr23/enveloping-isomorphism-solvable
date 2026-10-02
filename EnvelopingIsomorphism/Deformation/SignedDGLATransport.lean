import EnvelopingIsomorphism.Deformation.SignedDGLA

/-! Arity transport lemmas for actual signed differential graded Lie algebras. -/

namespace EnvelopingIsomorphism.Deformation

universe u v
variable {R : Type u} [CommRing R]

theorem gradedModuleCongr_heq (V : ℤ → ModuleCat.{v} R) {p q : ℤ}
    (h : p = q) (f : V p) : HEq (gradedModuleCongr R V h f) f := by
  subst q
  rfl

namespace SignedDGLA

variable (D : SignedDGLA.{u, v} R)

theorem bracket_cast_left {p p' q : ℤ} (hp : p = p') (f : D.Obj p) (g : D.Obj q) :
    D.bracket p' q (gradedModuleCongr R D.complex.X hp f) g =
      gradedModuleCongr R D.complex.X (congrArg (· + q) hp) (D.bracket p q f g) := by
  subst p'
  rfl

theorem d_cast {p q : ℤ} (h : p = q) (f : D.Obj p) :
    D.d q (gradedModuleCongr R D.complex.X h f) =
      gradedModuleCongr R D.complex.X (congrArg (· + 1) h) (D.d p f) := by
  subst q
  rfl

theorem d_bracket (p q : ℤ) (f : D.Obj p) (g : D.Obj q) :
    D.d (p + q) (D.bracket p q f g) =
      gradedModuleCongr R D.complex.X (by omega : (p + 1) + q = (p + q) + 1)
        (D.bracket (p + 1) q (D.d p f) g) +
      (p.negOnePow : R) • gradedModuleCongr R D.complex.X (add_assoc p q 1).symm
        (D.bracket p (q + 1) f (D.d q g)) :=
  D.differential_bracket p q f g

end SignedDGLA
end EnvelopingIsomorphism.Deformation
