import EnvelopingIsomorphism.Deformation.SchoutenAction
import EnvelopingIsomorphism.Deformation.Conjugation
import EnvelopingIsomorphism.Deformation.MaurerCartan
import EnvelopingIsomorphism.FormalSeries.BinaryAssociator
import Mathlib.Tactic.Module

/-! The genuine Schouten bracket of bivectors detects the ordinary Jacobi
identity, with the factor dictated by normalized HKR. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation

private theorem perm_three_univ : (Finset.univ : Finset (Equiv.Perm (Fin 3))) =
    {1, Equiv.swap 0 1, Equiv.swap 0 2, Equiv.swap 1 2,
      Equiv.swap 0 1 * Equiv.swap 1 2, Equiv.swap 1 2 * Equiv.swap 0 1} := by
  decide

section AlternatingThree

variable {k A : Type*} [CommRing k] [CommRing A] [Algebra k A]

theorem alternatingEvaluation_three (F : Cochain k A 3) (a : Fin 3 → A) :
    alternatingEvaluation F a =
      F ![a 0, a 1, a 2] - F ![a 1, a 0, a 2] - F ![a 2, a 1, a 0] -
        F ![a 0, a 2, a 1] + F ![a 1, a 2, a 0] + F ![a 2, a 0, a 1] := by
  have hv (b : Fin 3 → A) : b = ![b 0, b 1, b 2] := by
    funext i
    fin_cases i <;> rfl
  rw [alternatingEvaluation_apply]
  conv_lhs =>
    arg 2
    ext σ
    rw [hv (fun i ↦ a (σ i))]
  rw [perm_three_univ, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  simp [Equiv.Perm.sign_mul, Equiv.Perm.mul_apply, Equiv.swap_apply_def]
  abel

end AlternatingThree

section Jacobiator

open EnvelopingIsomorphism.FormalSeries.PowerSeriesModule

variable {k A : Type*} [CommRing k] [AddCommGroup A] [Module k A]

/-- The cyclic Jacobi insertion, with the outer bracket written on the left. -/
def jacobiInsert (μ ν : Binary k A) : Ternary k A :=
  insertLeft μ ν + rotateTernary (insertLeft μ ν) +
    rotateTernary (rotateTernary (insertLeft μ ν))

@[simp] theorem jacobiInsert_apply (μ ν : Binary k A) (a b c : A) :
    jacobiInsert μ ν a b c = μ (ν a b) c + μ (ν b c) a + μ (ν c a) b := rfl

theorem conjugate_jacobi (g : A ≃ₗ[k] A) (μ : Binary k A)
    (hμ : ∀ a b c, jacobiInsert μ μ a b c = 0) (a b c : A) :
    jacobiInsert (conjugate g μ) (conjugate g μ) a b c = 0 := by
  simp only [jacobiInsert_apply, conjugate_apply, LinearEquiv.symm_apply_apply]
  rw [← map_add, ← map_add]
  exact (congrArg g (hμ (g.symm a) (g.symm b) (g.symm c))).trans (map_zero g)

end Jacobiator

section Polynomial

universe u
variable {K : Type u} [Field K] [CharZero K] {d : ℕ}

omit [CharZero K] in
theorem rawBivector_skew (F : Multiderivation K (PolynomialFunctions K d) 2)
    (a b : PolynomialFunctions K d) : rawBivector F b a = -rawBivector F a b := by
  have h := F.val.map_swap (Fin.cons a (Fin.cons b Fin.elim0)) (by decide : (0 : Fin 2) ≠ 1)
  have hv : (Fin.cons a (Fin.cons b Fin.elim0) : Fin 2 → PolynomialFunctions K d) ∘
      Equiv.swap 0 1 = Fin.cons b (Fin.cons a Fin.elim0) := by
    funext i
    fin_cases i <;> rfl
  rw [hv] at h
  simpa only [rawBivector_apply] using h

theorem normalizedBivector_curried (F : Multiderivation K (PolynomialFunctions K d) 2) :
    cochainCurriedEquiv K (PolynomialFunctions K d) 2 (Multiderivation.toCochain F) =
      (2 : K)⁻¹ • rawBivector F := by
  rw [cochainCurriedEquiv_two]
  change cochainTwoEquiv K (PolynomialFunctions K d)
    ((Nat.factorial 2 : K)⁻¹ • F.val.toMultilinearMap) = _
  rw [map_smul]
  norm_num [Nat.factorial, rawBivector]

theorem cochainBracket_bivectors_apply
    (F G : Multiderivation K (PolynomialFunctions K d) 2)
    (a : Fin 3 → PolynomialFunctions K d) :
    cochainBracketPositive 1 1 (Multiderivation.toCochain F) (Multiderivation.toCochain G) a =
      (2 : K)⁻¹ • ((2 : K)⁻¹ • bracketBinary (rawBivector F) (rawBivector G) (a 0) (a 1) (a 2)) := by
  rw [cochainBracketPositive_apply, normalizedBivector_curried, normalizedBivector_curried,
    curriedBracket_binary_binary, cochainCurriedEquiv_three, cochainThreeEquiv_symm_apply]
  simp only [bracketBinary_apply, LinearMap.smul_apply, map_smul, smul_add, smul_sub, smul_smul]

/-- The normalized HKR convention gives the usual mixed Jacobi insertion. -/
theorem schoutenBivectors_apply
    (F G : Multiderivation K (PolynomialFunctions K d) 2)
    (a b c : PolynomialFunctions K d) :
    (show Multiderivation K (PolynomialFunctions K d) 3 from schoutenBracket K d 1 1 F G)
        ![a, b, c] =
      jacobiInsert (rawBivector F) (rawBivector G) a b c +
        jacobiInsert (rawBivector G) (rawBivector F) a b c := by
  refine (congrArg (fun H : PolynomialFunctions K d [⋀^Fin 3]→ₗ[K] PolynomialFunctions K d =>
    H ![a, b, c]) (schoutenBracket_nat_val 1 1 F G)).trans ?_
  change alternatingEvaluation
    (cochainBracketPositive 1 1 (Multiderivation.toCochain F) (Multiderivation.toCochain G)) ![a, b, c] = _
  rw [alternatingEvaluation_three]
  simp only [cochainBracket_bivectors_apply F G, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, bracketBinary_apply, jacobiInsert_apply]
  rw [rawBivector_skew F a b, rawBivector_skew F b c, rawBivector_skew F c a,
    rawBivector_skew G a b, rawBivector_skew G b c, rawBivector_skew G c a]
  simp only [map_neg, LinearMap.neg_apply]
  rw [rawBivector_skew F (rawBivector G a b) c,
    rawBivector_skew F (rawBivector G b c) a,
    rawBivector_skew F (rawBivector G c a) b,
    rawBivector_skew G (rawBivector F a b) c,
    rawBivector_skew G (rawBivector F b c) a,
    rawBivector_skew G (rawBivector F c a) b]
  module

def rawTrivector (F : Multiderivation K (PolynomialFunctions K d) 3) :
    Ternary K (PolynomialFunctions K d) :=
  cochainThreeEquiv K (PolynomialFunctions K d) F.val.toMultilinearMap

omit [CharZero K] in
theorem rawTrivector_apply (F : Multiderivation K (PolynomialFunctions K d) 3)
    (a b c : PolynomialFunctions K d) : rawTrivector F a b c = F ![a, b, c] := by
  have h := cochainThreeEquiv_symm_apply K (PolynomialFunctions K d)
    (cochainThreeEquiv K (PolynomialFunctions K d) F.val.toMultilinearMap) ![a, b, c]
  rw [LinearEquiv.symm_apply_apply] at h
  exact h.symm

def rawTrivectorLinearMap : Multiderivation K (PolynomialFunctions K d) 3 →ₗ[K]
    Ternary K (PolynomialFunctions K d) where
  toFun := rawTrivector
  map_add' F G := (cochainThreeEquiv K (PolynomialFunctions K d)).map_add F.val.toMultilinearMap G.val.toMultilinearMap
  map_smul' c F := (cochainThreeEquiv K (PolynomialFunctions K d)).map_smul c F.val.toMultilinearMap

omit [CharZero K] in
theorem rawTrivector_injective : Function.Injective (rawTrivector (K := K) (d := d)) := by
  intro F G h
  have he := (cochainThreeEquiv K (PolynomialFunctions K d)).injective h
  apply Multiderivation.ext
  intro a
  exact congrArg (fun C : Cochain K (PolynomialFunctions K d) 3 ↦ C a) he

omit [CharZero K] in
theorem rawBivector_injective : Function.Injective (rawBivector (K := K) (d := d)) := by
  intro F G h
  have he := (cochainTwoEquiv K (PolynomialFunctions K d)).injective h
  apply Multiderivation.ext
  intro a
  exact congrArg (fun C : Cochain K (PolynomialFunctions K d) 2 ↦ C a) he

theorem rawTrivector_schoutenBracket
    (F G : Multiderivation K (PolynomialFunctions K d) 2) :
    rawTrivector (show Multiderivation K (PolynomialFunctions K d) 3 from schoutenBracket K d 1 1 F G) =
      jacobiInsert (rawBivector F) (rawBivector G) + jacobiInsert (rawBivector G) (rawBivector F) := by
  apply LinearMap.ext
  intro a
  apply LinearMap.ext
  intro b
  apply LinearMap.ext
  intro c
  rw [rawTrivector_apply]
  exact schoutenBivectors_apply F G a b c

/-- The factor two in the Schouten square is retained explicitly. -/
theorem rawTrivector_schouten_self (F : Multiderivation K (PolynomialFunctions K d) 2) :
    rawTrivector (show Multiderivation K (PolynomialFunctions K d) 3 from schoutenBracket K d 1 1 F F) =
      (2 : K) • jacobiInsert (rawBivector F) (rawBivector F) := by
  rw [rawTrivector_schoutenBracket, two_smul]

theorem schoutenBivector_self_eq_zero_iff (F : Multiderivation K (PolynomialFunctions K d) 2) :
    (show Multiderivation K (PolynomialFunctions K d) 3 from schoutenBracket K d 1 1 F F) = 0 ↔
      ∀ a b c, jacobiInsert (rawBivector F) (rawBivector F) a b c = 0 := by
  constructor
  · intro h a b c
    have he := congrArg (fun T : Multiderivation K (PolynomialFunctions K d) 3 ↦ rawTrivector T a b c) h
    rw [rawTrivector_schouten_self] at he
    change (2 : K) • jacobiInsert (rawBivector F) (rawBivector F) a b c = 0 at he
    exact (smul_eq_zero.mp he).resolve_left two_ne_zero
  · intro h
    apply rawTrivector_injective
    rw [rawTrivector_schouten_self]
    apply LinearMap.ext
    intro a
    apply LinearMap.ext
    intro b
    apply LinearMap.ext
    intro c
    change (2 : K) • jacobiInsert (rawBivector F) (rawBivector F) a b c = 0
    rw [h, smul_zero]

/-- The genuine source Maurer-Cartan curvature evaluates to the ordinary Jacobiator. -/
theorem rawTrivector_schoutenCurvature (F : Multiderivation K (PolynomialFunctions K d) 2) :
    rawTrivector (show Multiderivation K (PolynomialFunctions K d) 3 from
      (polynomialSchoutenDGLA K d).curvature F) = jacobiInsert (rawBivector F) (rawBivector F) := by
  let B : Multiderivation K (PolynomialFunctions K d) 3 := schoutenBracket K d 1 1 F F
  have hB : rawTrivector B = (2 : K) • jacobiInsert (rawBivector F) (rawBivector F) :=
    rawTrivector_schouten_self F
  have hc : (show Multiderivation K (PolynomialFunctions K d) 3 from
      (polynomialSchoutenDGLA K d).curvature F) = (2 : K)⁻¹ • B := by
    change (0 : Multiderivation K (PolynomialFunctions K d) 3) + (2 : K)⁻¹ • B = _
    exact zero_add _
  rw [hc]
  change rawTrivectorLinearMap ((2 : K)⁻¹ • B) = _
  rw [map_smul]
  change (2 : K)⁻¹ • rawTrivector B = _
  rw [hB, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]

theorem polynomialSchouten_MC_iff_Jacobi (F : Multiderivation K (PolynomialFunctions K d) 2) :
    (polynomialSchoutenDGLA K d).IsMaurerCartan F ↔
      ∀ a b c, jacobiInsert (rawBivector F) (rawBivector F) a b c = 0 := by
  change (show Multiderivation K (PolynomialFunctions K d) 3 from
    (polynomialSchoutenDGLA K d).curvature F) = 0 ↔ _
  constructor
  · intro h a b c
    have he := congrArg rawTrivector h
    rw [rawTrivector_schoutenCurvature] at he
    exact congrArg (fun T : Ternary K (PolynomialFunctions K d) ↦ T a b c) he
  · intro h
    apply rawTrivector_injective
    rw [rawTrivector_schoutenCurvature]
    apply LinearMap.ext
    intro a
    apply LinearMap.ext
    intro b
    apply LinearMap.ext
    intro c
    exact h a b c

end Polynomial

end EnvelopingIsomorphism.Deformation
