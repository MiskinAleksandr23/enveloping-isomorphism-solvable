import EnvelopingIsomorphism.Deformation.SignedDGLA

/-!
# Projecting a differential graded Lie bracket to a zero-differential model

This module isolates the elementary Jacobi argument. Applications must provide
actual inclusion/projection maps and prove that replacing a closed element by
its chosen representative does not change the projected bracket.
-/

namespace EnvelopingIsomorphism.Deformation

universe u v w
variable {R : Type u} [CommRing R]

theorem gradedLinearMap_congr (V : ℤ → ModuleCat.{v} R) (W : ℤ → ModuleCat.{w} R)
    (f : (p : ℤ) → V p →ₗ[R] W p) {p q : ℤ} (h : p = q) (a : V p) :
    f q (gradedModuleCongr R V h a) = gradedModuleCongr R W h (f p a) := by
  subst q
  rfl

namespace SignedDGLA

variable (D : SignedDGLA.{u, v} R)

theorem bracket_closed (p q : ℤ) (f : D.Obj p) (g : D.Obj q)
    (hf : D.d p f = 0) (hg : D.d q g = 0) :
    D.d (p + q) (D.bracket p q f g) = 0 := by
  rw [d, D.differential_bracket]
  change _ + _ = 0
  change (D.complex.d p (p + 1)).hom f = 0 at hf
  change (D.complex.d q (q + 1)).hom g = 0 at hg
  rw [hf, hg]
  simp

theorem bracket_congr_left {p p' q : ℤ} (h : p = p') (f : D.Obj p) (g : D.Obj q) :
    D.bracket p' q (gradedModuleCongr R D.complex.X h f) g =
      gradedModuleCongr R D.complex.X (congrArg (· + q) h) (D.bracket p q f g) := by
  subst p'
  rfl

theorem bracket_congr_right {p q q' : ℤ} (h : q = q') (f : D.Obj p) (g : D.Obj q) :
    D.bracket p q' f (gradedModuleCongr R D.complex.X h g) =
      gradedModuleCongr R D.complex.X (congrArg (p + ·) h) (D.bracket p q f g) := by
  subst q'
  rfl

/-- A projection killing boundaries also kills their bracket with a closed element on the left. -/
theorem project_bracket_boundary_right (V : ℤ → ModuleCat.{w} R)
    (π : (p : ℤ) → D.Obj p →ₗ[R] V p)
    (hπ : ∀ p b, π (p + 1) (D.d p b) = 0)
    (p q : ℤ) (f : D.Obj p) (b : D.Obj q) (hf : D.d p f = 0) :
    π (p + (q + 1)) (D.bracket p (q + 1) f (D.d q b)) = 0 := by
  have hd := D.differential_bracket p q f b
  change (D.complex.d p (p + 1)).hom f = 0 at hf
  rw [hf] at hd
  simp only [map_zero, LinearMap.zero_apply, zero_add] at hd
  have hp := congrArg (π ((p + q) + 1)) hd
  change π ((p + q) + 1) (D.d (p + q) (D.bracket p q f b)) = _ at hp
  rw [hπ, map_smul, gradedLinearMap_congr] at hp
  have hsign : (p.negOnePow : R) * (p.negOnePow : R) = 1 := by
    have hs := congrArg (fun z : ℤˣ => ((z : ℤ) : R)) (Int.units_mul_self p.negOnePow)
    simpa only [Units.val_mul, Int.cast_mul, Units.val_one, Int.cast_one] using hs
  have hh := congrArg (fun z => (p.negOnePow : R) • z) hp
  rw [smul_zero, smul_smul, hsign, one_smul] at hh
  apply (gradedModuleCongr R V (add_assoc p q 1).symm).injective
  simpa only [map_zero, d] using hh.symm

/-- The corresponding boundary-annihilation statement with the boundary on the left. -/
theorem project_bracket_boundary_left (V : ℤ → ModuleCat.{w} R)
    (π : (p : ℤ) → D.Obj p →ₗ[R] V p)
    (hπ : ∀ p b, π (p + 1) (D.d p b) = 0)
    (p q : ℤ) (b : D.Obj p) (g : D.Obj q) (hg : D.d q g = 0) :
    π ((p + 1) + q) (D.bracket (p + 1) q (D.d p b) g) = 0 := by
  have hd := D.differential_bracket p q b g
  change (D.complex.d q (q + 1)).hom g = 0 at hg
  rw [hg] at hd
  simp only [map_zero, smul_zero, add_zero] at hd
  have hp := congrArg (π ((p + q) + 1)) hd
  change π ((p + q) + 1) (D.d (p + q) (D.bracket p q b g)) = _ at hp
  rw [hπ, gradedLinearMap_congr] at hp
  apply (gradedModuleCongr R V (by omega : (p + 1) + q = (p + q) + 1)).injective
  simpa only [map_zero, d] using hp.symm

/-- Concrete data sufficient to transfer the bracket to a zero-differential model. -/
structure ProjectedModel where
  obj : ℤ → ModuleCat.{w} R
  inclusion : (p : ℤ) → obj p →ₗ[R] D.Obj p
  projection : (p : ℤ) → D.Obj p →ₗ[R] obj p
  closed (p : ℤ) (f : obj p) : D.d p (inclusion p f) = 0
  project_left (p q : ℤ) (f : obj p) (c : D.Obj q) (hc : D.d q c = 0) :
    projection (p + q) (D.bracket p q (inclusion p f) (inclusion q (projection q c))) =
      projection (p + q) (D.bracket p q (inclusion p f) c)
  project_right (p q : ℤ) (c : D.Obj p) (g : obj q) (hc : D.d p c = 0) :
    projection (p + q) (D.bracket p q (inclusion p (projection p c)) (inclusion q g)) =
      projection (p + q) (D.bracket p q c (inclusion q g))

namespace ProjectedModel

variable {D} (S : D.ProjectedModel.{u, v, w})

def bracket (p q : ℤ) : S.obj p →ₗ[R] S.obj q →ₗ[R] S.obj (p + q) :=
  (((D.bracket p q).comp (S.inclusion p)).compl₂ (S.inclusion q)).compr₂ (S.projection (p + q))

@[simp] theorem bracket_apply (p q : ℤ) (f : S.obj p) (g : S.obj q) :
    S.bracket p q f g = S.projection (p + q) (D.bracket p q (S.inclusion p f) (S.inclusion q g)) :=
  rfl

theorem projection_congr {p q : ℤ} (h : p = q) (f : D.Obj p) :
    S.projection q (gradedModuleCongr R D.complex.X h f) =
      gradedModuleCongr R S.obj h (S.projection p f) := by
  subst q
  rfl

theorem projection_heq {p q : ℤ} (h : p = q) {f : D.Obj p} {g : D.Obj q} (hfg : HEq f g) :
    HEq (S.projection p f) (S.projection q g) := by
  subst q
  have he := eq_of_heq hfg
  rw [he]

theorem skew (p q : ℤ) (f : S.obj p) (g : S.obj q) :
    HEq (S.bracket p q f g) (-((p * q).negOnePow : R) • S.bracket q p g f) := by
  have h := S.projection_heq (add_comm p q) (D.skew p q (S.inclusion p f) (S.inclusion q g))
  simpa only [bracket_apply, map_smul] using h

theorem jacobi (p q r : ℤ) (f : S.obj p) (g : S.obj q) (h : S.obj r) :
    gradedModuleCongr R S.obj (add_assoc p q r).symm (S.bracket p (q + r) f (S.bracket q r g h)) =
      S.bracket (p + q) r (S.bracket p q f g) h +
        ((p * q).negOnePow : R) • gradedModuleCongr R S.obj
          (by omega : q + (p + r) = (p + q) + r) (S.bracket q (p + r) g (S.bracket p r f h)) := by
  simp only [bracket_apply]
  rw [S.project_left p (q + r) f _
      (D.bracket_closed q r _ _ (S.closed q g) (S.closed r h)),
    S.project_right (p + q) r _ h
      (D.bracket_closed p q _ _ (S.closed p f) (S.closed q g)),
    S.project_left q (p + r) g _
      (D.bracket_closed p r _ _ (S.closed p f) (S.closed r h)),
    ← S.projection_congr, ← S.projection_congr, ← map_smul, ← map_add]
  exact congrArg (S.projection ((p + q) + r))
    (D.jacobi p q r (S.inclusion p f) (S.inclusion q g) (S.inclusion r h))

def complex : CochainComplex (ModuleCat.{w} R) ℤ :=
  CochainComplex.of S.obj (fun _ => 0) (fun _ => by simp)

@[simp] theorem complex_d (p q : ℤ) : S.complex.d p q = 0 := by
  simp [complex, CochainComplex.of.d]
  rfl

/-- All signed DGLA identities follow from the proved representative-compatibility conditions. -/
def toSignedDGLA : SignedDGLA.{u, w} R where
  complex := S.complex
  bracket := S.bracket
  skew := S.skew
  jacobi := S.jacobi
  differential_bracket := by
    intro p q f g
    simp only [complex_d]
    change 0 = _
    simp

end ProjectedModel

/-- Actual correction by boundaries proves all representative-compatibility conditions. -/
def projectedModelOfCycleCorrection
    (V : ℤ → ModuleCat.{w} R) (ι : (p : ℤ) → V p →ₗ[R] D.Obj p)
    (π : (p : ℤ) → D.Obj p →ₗ[R] V p)
    (hι : ∀ p f, D.d p (ι p f) = 0)
    (hπ : ∀ p b, π (p + 1) (D.d p b) = 0)
    (hc : ∀ p c, D.d p c = 0 → ∃ b : D.Obj (p - 1),
      c - ι p (π p c) =
        gradedModuleCongr R D.complex.X (by omega : (p - 1) + 1 = p) (D.d (p - 1) b)) :
    D.ProjectedModel where
  obj := V
  inclusion := ι
  projection := π
  closed := hι
  project_left := by
    intro p q f c hclosed
    obtain ⟨b, hb⟩ := hc q c hclosed
    have hh := congrArg (fun y => π (p + q) (D.bracket p q (ι p f) y)) hb
    simp only [map_sub] at hh
    rw [D.bracket_congr_right, gradedLinearMap_congr,
      D.project_bracket_boundary_right V π hπ p (q - 1) (ι p f) b (hι p f), map_zero] at hh
    exact (sub_eq_zero.mp hh).symm
  project_right := by
    intro p q c g hclosed
    obtain ⟨b, hb⟩ := hc p c hclosed
    have hh := congrArg (fun x => π (p + q) (D.bracket p q x (ι q g))) hb
    simp only [map_sub, LinearMap.sub_apply] at hh
    rw [D.bracket_congr_left, gradedLinearMap_congr,
      D.project_bracket_boundary_left V π hπ (p - 1) q b (ι q g) (hι q g), map_zero] at hh
    exact (sub_eq_zero.mp hh).symm

end SignedDGLA

end EnvelopingIsomorphism.Deformation
