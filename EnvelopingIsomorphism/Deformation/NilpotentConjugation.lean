import EnvelopingIsomorphism.Deformation.Conjugation
import Mathlib.RingTheory.Nilpotent.Exp

/-! Exponentiating the unary Hochschild action agrees with actual conjugation
of an arbitrary bilinear product. This finite statement needs only nilpotence
of the acting operator, and applies to every finite formal jet. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.NilpotentConjugation

variable {k A : Type*} [CommRing k] [AddCommGroup A] [Module k A]

def output (X : Module.End k A) : Module.End k (Binary k A) where
  toFun μ := μ.compr₂ X
  map_add' μ ν := by ext a b; simp
  map_smul' c μ := by ext a b; simp

def inputLeft (X : Module.End k A) : Module.End k (Binary k A) where
  toFun μ := μ.comp X
  map_add' μ ν := by ext a b; simp
  map_smul' c μ := by ext a b; simp

def inputRight (X : Module.End k A) : Module.End k (Binary k A) where
  toFun μ := μ.compl₂ X
  map_add' μ ν := by ext a b; simp
  map_smul' c μ := by ext a b; simp

@[simp] theorem output_apply (X : Module.End k A) (μ : Binary k A) (a b : A) :
    output X μ a b = X (μ a b) := rfl

@[simp] theorem inputLeft_apply (X : Module.End k A) (μ : Binary k A) (a b : A) :
    inputLeft X μ a b = μ (X a) b := rfl

@[simp] theorem inputRight_apply (X : Module.End k A) (μ : Binary k A) (a b : A) :
    inputRight X μ a b = μ a (X b) := rfl

def unaryActionEnd (X : Module.End k A) : Module.End k (Binary k A) :=
  output X - inputLeft X - inputRight X

@[simp] theorem unaryActionEnd_apply (X : Module.End k A) (μ : Binary k A) :
    unaryActionEnd X μ = unaryAction X μ := rfl

theorem output_inputLeft_commute (X Y : Module.End k A) : Commute (output X) (inputLeft Y) := by
  ext μ a b
  rfl

theorem output_inputRight_commute (X Y : Module.End k A) : Commute (output X) (inputRight Y) := by
  ext μ a b
  rfl

theorem inputLeft_inputRight_commute (X Y : Module.End k A) :
    Commute (inputLeft X) (inputRight Y) := by
  ext μ a b
  rfl

@[simp] theorem output_neg (X : Module.End k A) : output (-X) = -output X := by
  ext μ a b
  simp

@[simp] theorem inputLeft_neg (X : Module.End k A) : inputLeft (-X) = -inputLeft X := by
  ext μ a b
  simp

@[simp] theorem inputRight_neg (X : Module.End k A) : inputRight (-X) = -inputRight X := by
  ext μ a b
  simp

theorem output_pow_apply (X : Module.End k A) (n : ℕ) (μ : Binary k A) (a b : A) :
    (output X ^ n) μ a b = (X ^ n) (μ a b) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, output_apply, ih, pow_succ', Module.End.mul_apply]

theorem inputLeft_pow_apply (X : Module.End k A) (n : ℕ) (μ : Binary k A) (a b : A) :
    (inputLeft X ^ n) μ a b = μ ((X ^ n) a) b := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, inputLeft_apply, ih, pow_succ, Module.End.mul_apply]

theorem inputRight_pow_apply (X : Module.End k A) (n : ℕ) (μ : Binary k A) (a b : A) :
    (inputRight X ^ n) μ a b = μ a ((X ^ n) b) := by
  induction n generalizing b with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, inputRight_apply, ih, pow_succ, Module.End.mul_apply]

theorem output_pow_eq_zero {X : Module.End k A} {n : ℕ} (h : X ^ n = 0) : output X ^ n = 0 := by
  ext μ a b
  simp [output_pow_apply, h]

theorem inputLeft_pow_eq_zero {X : Module.End k A} {n : ℕ} (h : X ^ n = 0) :
    inputLeft X ^ n = 0 := by
  ext μ a b
  simp [inputLeft_pow_apply, h]

theorem inputRight_pow_eq_zero {X : Module.End k A} {n : ℕ} (h : X ^ n = 0) :
    inputRight X ^ n = 0 := by
  ext μ a b
  simp [inputRight_pow_apply, h]

theorem isNilpotent_output {X : Module.End k A} (hX : IsNilpotent X) :
    IsNilpotent (output X) := by
  obtain ⟨n, hn⟩ := hX
  exact ⟨n, output_pow_eq_zero hn⟩

theorem isNilpotent_inputLeft {X : Module.End k A} (hX : IsNilpotent X) :
    IsNilpotent (inputLeft X) := by
  obtain ⟨n, hn⟩ := hX
  exact ⟨n, inputLeft_pow_eq_zero hn⟩

theorem isNilpotent_inputRight {X : Module.End k A} (hX : IsNilpotent X) :
    IsNilpotent (inputRight X) := by
  obtain ⟨n, hn⟩ := hX
  exact ⟨n, inputRight_pow_eq_zero hn⟩

theorem isNilpotent_unaryActionEnd {X : Module.End k A} (hX : IsNilpotent X) :
    IsNilpotent (unaryActionEnd X) := by
  change IsNilpotent (output X - inputLeft X - inputRight X)
  have hl : IsNilpotent (output X - inputLeft X) :=
    Commute.isNilpotent_sub (R := Module.End k (Binary k A)) (output_inputLeft_commute X X)
      (isNilpotent_output hX) (isNilpotent_inputLeft hX)
  have hc : Commute (output X - inputLeft X) (inputRight X) :=
    by
      ext μ a b
      simp only [Module.End.mul_apply, LinearMap.sub_apply,
        output_apply, inputLeft_apply, inputRight_apply, map_sub]
  exact Commute.isNilpotent_sub (R := Module.End k (Binary k A)) hc hl (isNilpotent_inputRight hX)

section Rational

variable [Algebra ℚ k] [Module ℚ A]

/-- The finite exponential of the unary action, bundled before specialization
to quotient modules so its additive structures remain coherent. -/
def adjointExponential (X : Module.End k A) : Module.End k (Binary k A) :=
  IsNilpotent.exp (unaryActionEnd X)

theorem exp_output_apply {X : Module.End k A} (hX : IsNilpotent X)
    (μ : Binary k A) (a b : A) :
    IsNilpotent.exp (output X) μ a b = IsNilpotent.exp X (μ a b) := by
  obtain ⟨n, hn⟩ := hX
  rw [IsNilpotent.exp_eq_sum (output_pow_eq_zero hn), IsNilpotent.exp_eq_sum hn]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, output_pow_apply]

theorem exp_inputLeft_apply {X : Module.End k A} (hX : IsNilpotent X)
    (μ : Binary k A) (a b : A) :
    IsNilpotent.exp (inputLeft X) μ a b = μ (IsNilpotent.exp X a) b := by
  obtain ⟨n, hn⟩ := hX
  rw [IsNilpotent.exp_eq_sum (inputLeft_pow_eq_zero hn), IsNilpotent.exp_eq_sum hn]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, inputLeft_pow_apply, map_sum,
    map_rat_smul]

theorem exp_inputRight_apply {X : Module.End k A} (hX : IsNilpotent X)
    (μ : Binary k A) (a b : A) :
    IsNilpotent.exp (inputRight X) μ a b = μ a (IsNilpotent.exp X b) := by
  obtain ⟨n, hn⟩ := hX
  rw [IsNilpotent.exp_eq_sum (inputRight_pow_eq_zero hn), IsNilpotent.exp_eq_sum hn]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, inputRight_pow_apply, map_sum,
    map_rat_smul]

/-- The three commuting actions factor the exponential of the Hochschild
unary action into actual output and input coordinate changes. -/
theorem exp_unaryActionEnd_apply {X : Module.End k A} (hX : IsNilpotent X)
    (μ : Binary k A) (a b : A) :
    IsNilpotent.exp (unaryActionEnd X) μ a b =
      IsNilpotent.exp X (μ (IsNilpotent.exp (-X) a) (IsNilpotent.exp (-X) b)) := by
  have h₁ := output_inputLeft_commute X (-X)
  have h₂ := (output_inputRight_commute X (-X)).add_left
    (inputLeft_inputRight_commute (-X) (-X))
  have heq : unaryActionEnd X = output X + inputLeft (-X) + inputRight (-X) := by
    rw [unaryActionEnd, inputLeft_neg, inputRight_neg]
    abel
  rw [heq, IsNilpotent.exp_add_of_commute h₂
    (h₁.isNilpotent_add (isNilpotent_output hX) (isNilpotent_inputLeft hX.neg))
    (isNilpotent_inputRight hX.neg),
    IsNilpotent.exp_add_of_commute h₁ (isNilpotent_output hX) (isNilpotent_inputLeft hX.neg),
    Module.End.mul_apply, Module.End.mul_apply, exp_output_apply hX,
    exp_inputLeft_apply hX.neg, exp_inputRight_apply hX.neg]

/-- The actual linear coordinate change underlying a nilpotent exponential. -/
def expEquiv (X : Module.End k A) (hX : IsNilpotent X) : A ≃ₗ[k] A where
  toFun := (IsNilpotent.exp X : Module.End k A)
  invFun := (IsNilpotent.exp (-X) : Module.End k A)
  left_inv a := by
    have h := LinearMap.congr_fun (IsNilpotent.exp_neg_mul_exp_self hX) a
    exact h
  right_inv a := by
    have h := LinearMap.congr_fun (IsNilpotent.exp_mul_exp_neg_self hX) a
    exact h
  map_add' := (IsNilpotent.exp X).map_add
  map_smul' := (IsNilpotent.exp X).map_smul

@[simp] theorem expEquiv_apply (X : Module.End k A) (hX : IsNilpotent X) (a : A) :
    expEquiv X hX a = IsNilpotent.exp X a := rfl

@[simp] theorem expEquiv_symm_apply (X : Module.End k A) (hX : IsNilpotent X) (a : A) :
    (expEquiv X hX).symm a = IsNilpotent.exp (-X) a := rfl

/-- Finite genuine gauge transport equals the exponential of `[X,-]`, with
the output-minus-inputs sign convention used in the Hochschild complex. -/
theorem conjugate_expEquiv {X : Module.End k A} (hX : IsNilpotent X) (μ : Binary k A) :
    conjugate (expEquiv X hX) μ = IsNilpotent.exp (unaryActionEnd X) μ := by
  ext a b
  simpa only [conjugate_apply, expEquiv_apply, expEquiv_symm_apply] using
    (exp_unaryActionEnd_apply hX μ a b).symm

end Rational

end EnvelopingIsomorphism.Deformation.NilpotentConjugation
