import EnvelopingIsomorphism.Deformation.MaurerCartan
import EnvelopingIsomorphism.Deformation.SignedDGLATransport

/-! Twisting the actual differential by a degree-one Maurer-Cartan element. -/

namespace EnvelopingIsomorphism.Deformation.SignedDGLA

universe u v
variable {K : Type u} [Field K] (D : SignedDGLA.{u, v} K)

/-- The adjoint operator of a degree-one element, in the differential's degree convention. -/
def oddAdjoint (α : D.Obj 1) (p : ℤ) : D.Obj p →ₗ[K] D.Obj (p + 1) :=
  (gradedModuleCongr K D.complex.X (add_comm 1 p)).toLinearMap.comp (D.bracket 1 p α)

@[simp] theorem oddAdjoint_apply (α : D.Obj 1) (p : ℤ) (x : D.Obj p) :
    D.oddAdjoint α p x = gradedModuleCongr K D.complex.X (add_comm 1 p) (D.bracket 1 p α x) := rfl

/-- Adjoint of a degree-two element, with the target degree of two differentials. -/
def evenAdjoint (β : D.Obj 2) (p : ℤ) : D.Obj p →ₗ[K] D.Obj ((p + 1) + 1) :=
  (gradedModuleCongr K D.complex.X (by omega : 2 + p = (p + 1) + 1)).toLinearMap.comp
    (D.bracket 2 p β)

@[simp] theorem evenAdjoint_apply (β : D.Obj 2) (p : ℤ) (x : D.Obj p) :
    D.evenAdjoint β p x = gradedModuleCongr K D.complex.X
      (by omega : 2 + p = (p + 1) + 1) (D.bracket 2 p β x) := rfl

def degreeOneDifferential (α : D.Obj 1) : D.Obj 2 :=
  gradedModuleCongr K D.complex.X (by decide : (1 : ℤ) + 1 = 2) (D.d 1 α)

def degreeOneSquareBracket (α : D.Obj 1) : D.Obj 2 :=
  gradedModuleCongr K D.complex.X (by decide : (1 : ℤ) + 1 = 2) (D.bracket 1 1 α α)

theorem evenAdjoint_cast (β : D.Obj (1 + 1)) (p : ℤ) (x : D.Obj p) :
    D.evenAdjoint (gradedModuleCongr K D.complex.X (by decide : (1 : ℤ) + 1 = 2) β) p x =
      gradedModuleCongr K D.complex.X (by omega : (1 + 1) + p = (p + 1) + 1)
        (D.bracket (1 + 1) p β x) := by
  rw [evenAdjoint_apply, D.bracket_cast_left, gradedModuleCongr_trans]

theorem evenAdjoint_add (β γ : D.Obj 2) (p : ℤ) (x : D.Obj p) :
    D.evenAdjoint (β + γ) p x = D.evenAdjoint β p x + D.evenAdjoint γ p x := by
  simp only [evenAdjoint_apply, map_add, LinearMap.add_apply]

theorem evenAdjoint_smul (c : K) (β : D.Obj 2) (p : ℤ) (x : D.Obj p) :
    D.evenAdjoint (c • β) p x = c • D.evenAdjoint β p x := by
  simp only [evenAdjoint_apply, map_smul, LinearMap.smul_apply]

theorem oddAdjoint_comp (α : D.Obj 1) (p : ℤ) (x : D.Obj p) :
    D.oddAdjoint α (p + 1) (D.oddAdjoint α p x) =
      gradedModuleCongr K D.complex.X (by omega : 1 + (1 + p) = (p + 1) + 1)
        (D.bracket 1 (1 + p) α (D.bracket 1 p α x)) := by
  rw [oddAdjoint_apply, oddAdjoint_apply, D.bracket_cast_right, gradedModuleCongr_trans]

/-- Odd adjoint square, before dividing by two. -/
theorem oddAdjoint_sq_two (α : D.Obj 1) (p : ℤ) (x : D.Obj p) :
    (2 : K) • D.oddAdjoint α (p + 1) (D.oddAdjoint α p x) =
      D.evenAdjoint (D.degreeOneSquareBracket α) p x := by
  have hj := congrArg
    (gradedModuleCongr K D.complex.X (by omega : (1 + 1) + p = (p + 1) + 1))
    (D.jacobi 1 1 p α α x)
  have hs : (((1 : ℤ) * 1).negOnePow : K) = -1 := by norm_num
  simp only [map_add, map_neg, gradedModuleCongr_trans, hs, neg_one_smul] at hj
  simp only [← D.oddAdjoint_comp] at hj
  rw [← D.evenAdjoint_cast] at hj
  change D.oddAdjoint α (p + 1) (D.oddAdjoint α p x) =
    D.evenAdjoint (D.degreeOneSquareBracket α) p x +
      -D.oddAdjoint α (p + 1) (D.oddAdjoint α p x) at hj
  rw [two_smul]
  calc
    _ = (D.evenAdjoint (D.degreeOneSquareBracket α) p x +
          -D.oddAdjoint α (p + 1) (D.oddAdjoint α p x)) +
          D.oddAdjoint α (p + 1) (D.oddAdjoint α p x) := congrArg (· + _) hj
    _ = _ := by abel

theorem oddAdjoint_sq [CharZero K] (α : D.Obj 1) (p : ℤ) (x : D.Obj p) :
    D.oddAdjoint α (p + 1) (D.oddAdjoint α p x) =
      (2 : K)⁻¹ • D.evenAdjoint (D.degreeOneSquareBracket α) p x := by
  have h := congrArg (fun z : D.Obj ((p + 1) + 1) ↦ (2 : K)⁻¹ • z) (D.oddAdjoint_sq_two α p x)
  simpa only [smul_smul, inv_mul_cancel₀ (show (2 : K) ≠ 0 from two_ne_zero), one_smul] using h

/-- The differential anticommutes with odd adjoint, up to the adjoint of dα. -/
theorem d_oddAdjoint (α : D.Obj 1) (p : ℤ) (x : D.Obj p) :
    D.d (p + 1) (D.oddAdjoint α p x) =
      D.evenAdjoint (D.degreeOneDifferential α) p x - D.oddAdjoint α (p + 1) (D.d p x) := by
  rw [oddAdjoint_apply, D.d_cast, D.d_bracket]
  have hs : ((1 : ℤ).negOnePow : K) = -1 := by norm_num
  simp only [map_add, map_neg, gradedModuleCongr_trans, hs, neg_one_smul, sub_eq_add_neg]
  rw [← D.evenAdjoint_cast]
  rfl

/-- The candidate twisted differential is the original differential plus odd adjoint. -/
def twistedD (α : D.Obj 1) (p : ℤ) : D.Obj p →ₗ[K] D.Obj (p + 1) :=
  D.d p + D.oddAdjoint α p

@[simp] theorem twistedD_apply (α : D.Obj 1) (p : ℤ) (x : D.Obj p) :
    D.twistedD α p x = D.d p x + D.oddAdjoint α p x := rfl

/-- The square of the actual twisted differential is the adjoint of the MC curvature. -/
theorem twistedD_sq [CharZero K] (α : D.Obj 1) (p : ℤ) (x : D.Obj p) :
    D.twistedD α (p + 1) (D.twistedD α p x) = D.evenAdjoint (D.curvature α) p x := by
  simp only [twistedD_apply, map_add, D.d_sq, zero_add, D.d_oddAdjoint, D.oddAdjoint_sq]
  have hcurv : D.curvature α = D.degreeOneDifferential α + (2 : K)⁻¹ • D.degreeOneSquareBracket α := by
    unfold curvature degreeOneDifferential degreeOneSquareBracket
    rw [map_add, map_smul]
  rw [hcurv, evenAdjoint_add, evenAdjoint_smul]
  abel

theorem twistedD_sq_zero [CharZero K] (α : D.Obj 1) (hα : D.IsMaurerCartan α) (p : ℤ) (x : D.Obj p) :
    D.twistedD α (p + 1) (D.twistedD α p x) = 0 := by
  rw [D.twistedD_sq, hα]
  simp only [evenAdjoint_apply, map_zero, LinearMap.zero_apply]

/-- Odd adjoint is a graded derivation of the bracket, by the actual Jacobi identity. -/
theorem oddAdjoint_bracket (α : D.Obj 1) (p q : ℤ) (f : D.Obj p) (g : D.Obj q) :
    D.oddAdjoint α (p + q) (D.bracket p q f g) =
      gradedModuleCongr K D.complex.X (by omega : (p + 1) + q = (p + q) + 1)
        (D.bracket (p + 1) q (D.oddAdjoint α p f) g) +
      (p.negOnePow : K) • gradedModuleCongr K D.complex.X (add_assoc p q 1).symm
        (D.bracket p (q + 1) f (D.oddAdjoint α q g)) := by
  have hj := congrArg
    (gradedModuleCongr K D.complex.X (by omega : (1 + p) + q = (p + q) + 1))
    (D.jacobi 1 p q α f g)
  simp only [map_add, map_smul, gradedModuleCongr_trans, Int.one_mul] at hj
  simp only [oddAdjoint_apply, D.bracket_cast_left, D.bracket_cast_right, gradedModuleCongr_trans]
  exact hj

/-- The candidate twisted differential obeys the graded Leibniz law even before imposing MC. -/
theorem twistedD_bracket (α : D.Obj 1) (p q : ℤ) (f : D.Obj p) (g : D.Obj q) :
    D.twistedD α (p + q) (D.bracket p q f g) =
      gradedModuleCongr K D.complex.X (by omega : (p + 1) + q = (p + q) + 1)
        (D.bracket (p + 1) q (D.twistedD α p f) g) +
      (p.negOnePow : K) • gradedModuleCongr K D.complex.X (add_assoc p q 1).symm
        (D.bracket p (q + 1) f (D.twistedD α q g)) := by
  rw [twistedD_apply, D.d_bracket, D.oddAdjoint_bracket]
  simp only [twistedD_apply, map_add, LinearMap.add_apply, smul_add]
  abel

/-- The twisted differential defines an actual Mathlib cochain complex. -/
def twistedComplex [CharZero K] (α : D.Obj 1) (hα : D.IsMaurerCartan α) :
    CochainComplex (ModuleCat.{v} K) ℤ :=
  CochainComplex.of D.complex.X (fun p ↦ ModuleCat.ofHom (D.twistedD α p)) (by
    intro p
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact D.twistedD_sq_zero α hα p x)

@[simp] theorem twistedComplex_d [CharZero K] (α : D.Obj 1) (hα : D.IsMaurerCartan α) (p : ℤ) :
    ((D.twistedComplex α hα).d p (p + 1)).hom = D.twistedD α p := by
  simp only [twistedComplex, CochainComplex.of_d]
  rfl

/-- Maurer-Cartan twisting preserves the bracket and replaces d by d+[α,-]. -/
def twist [CharZero K] (α : D.Obj 1) (hα : D.IsMaurerCartan α) : SignedDGLA.{u, v} K where
  complex := D.twistedComplex α hα
  bracket := D.bracket
  skew := D.skew
  jacobi := D.jacobi
  differential_bracket p q f g := by
    simp only [twistedComplex_d]
    exact D.twistedD_bracket α p q f g

@[simp] theorem twist_d [CharZero K] (α : D.Obj 1) (hα : D.IsMaurerCartan α) (p : ℤ) :
    (D.twist α hα).d p = D.twistedD α p := D.twistedComplex_d α hα p

@[simp] theorem twist_bracket [CharZero K] (α : D.Obj 1) (hα : D.IsMaurerCartan α)
    (p q : ℤ) (f : D.Obj p) (g : D.Obj q) :
    (D.twist α hα).bracket p q f g = D.bracket p q f g := rfl

@[simp] theorem twistedD_zero (p : ℤ) : D.twistedD (0 : D.Obj 1) p = D.d p := by
  apply LinearMap.ext
  intro x
  simp only [twistedD_apply, oddAdjoint_apply, map_zero, LinearMap.zero_apply, add_zero]

theorem bracket_one_symmetric (α β : D.Obj 1) : D.bracket 1 1 α β = D.bracket 1 1 β α := by
  have h := eq_of_heq (D.skew 1 1 α β)
  have hs : -(((1 : ℤ) * 1).negOnePow : K) = 1 := by norm_num
  simpa only [hs, one_smul] using h

/-- Twisting changes curvature by translating its base point. -/
theorem twist_curvature [CharZero K] (α : D.Obj 1) (hα : D.IsMaurerCartan α) (β : D.Obj 1) :
    (D.twist α hα).curvature β = D.curvature (α + β) - D.curvature α := by
  unfold curvature
  rw [D.twist_d, D.twist_bracket]
  change gradedModuleCongr K D.complex.X (by decide : (1 : ℤ) + 1 = 2)
      (D.twistedD α 1 β + (2 : K)⁻¹ • D.bracket 1 1 β β) =
    gradedModuleCongr K D.complex.X (by decide : (1 : ℤ) + 1 = 2)
      (D.d 1 (α + β) + (2 : K)⁻¹ • D.bracket 1 1 (α + β) (α + β)) -
    gradedModuleCongr K D.complex.X (by decide : (1 : ℤ) + 1 = 2)
      (D.d 1 α + (2 : K)⁻¹ • D.bracket 1 1 α α)
  rw [← map_sub, twistedD_apply, oddAdjoint_apply]
  apply congrArg (gradedModuleCongr K D.complex.X (by decide : (1 : ℤ) + 1 = 2))
  change D.d 1 β + D.bracket 1 1 α β + (2 : K)⁻¹ • D.bracket 1 1 β β =
    (D.d 1 (α + β) + (2 : K)⁻¹ • D.bracket 1 1 (α + β) (α + β)) -
      (D.d 1 α + (2 : K)⁻¹ • D.bracket 1 1 α α)
  have hcross : (2 : K)⁻¹ • D.bracket 1 1 α β + (2 : K)⁻¹ • D.bracket 1 1 β α =
      D.bracket 1 1 α β := by
    rw [D.bracket_one_symmetric β α, ← smul_add, ← two_smul K (D.bracket 1 1 α β), smul_smul,
      inv_mul_cancel₀ (show (2 : K) ≠ 0 from two_ne_zero), one_smul]
  simp only [map_add, LinearMap.add_apply, smul_add]
  calc
    _ = D.d 1 β + ((2 : K)⁻¹ • D.bracket 1 1 α β + (2 : K)⁻¹ • D.bracket 1 1 β α) +
          (2 : K)⁻¹ • D.bracket 1 1 β β := by rw [hcross]
    _ = _ := by abel

/-- Maurer-Cartan elements of the twist correspond exactly to translated MC elements. -/
theorem twist_isMaurerCartan_iff [CharZero K] (α : D.Obj 1) (hα : D.IsMaurerCartan α)
    (β : D.Obj 1) : (D.twist α hα).IsMaurerCartan β ↔ D.IsMaurerCartan (α + β) := by
  change (D.twist α hα).curvature β = 0 ↔ D.curvature (α + β) = 0
  rw [D.twist_curvature, hα, sub_zero]
  rfl

end EnvelopingIsomorphism.Deformation.SignedDGLA
