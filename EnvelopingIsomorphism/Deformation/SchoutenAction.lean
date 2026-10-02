import EnvelopingIsomorphism.Deformation.Schouten

/-!
# Vector-field action on polynomial multiderivations

The degree-zero Schouten action is computed on polynomial arguments by the
ordinary Lie-derivative formula, using the actual insertion operations.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation

open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

section LinearAction

variable {R A : Type*} [CommRing R] [AddCommGroup A] [Module R A]

/-- Inserting a unary map in every slot is the sum of the actual updated-tuple evaluations. -/
theorem curriedPreLie_unary_eval (n : ℕ) (F : Curried R A (n + 1)) (X : Unary R A)
    (a : Fin (n + 1) → A) :
    curriedEval (n + 1) (curriedPreLie 1 n F X) a =
      ∑ i : Fin (n + 1), curriedEval (n + 1) F (Function.update a i (X (a i))) := by
  induction n with
  | zero =>
    change F (X (a 0)) = ∑ i : Fin 1, F (Function.update a i (X (a i)) 0)
    simp
  | succ n ih =>
    have hh : curriedPreLie 1 (n + 1) F X (a 0) =
        F (X (a 0)) + curriedPreLie 1 n (F (a 0)) X := by
      change F (X (a 0)) + (-1 : R) ^ 2 • curriedPreLie 1 n (F (a 0)) X = _
      rw [neg_one_sq, one_smul]
    change curriedEval (n + 1) (curriedPreLie 1 (n + 1) F X (a 0)) (Fin.tail a) = _
    rw [hh, curriedEval_add, ih]
    conv_rhs => rw [Fin.sum_univ_succ]
    apply congrArg₂ (· + ·)
    · simp only [curriedEval, Function.update_self, Fin.tail_update_zero]
    · apply Finset.sum_congr rfl
      intro i hi
      change curriedEval (n + 1) (F (a 0))
        (Function.update (Fin.tail a) i (X (Fin.tail a i))) =
          curriedEval (n + 1) (F (Function.update a i.succ (X (a i.succ)) 0))
            (Fin.tail (Function.update a i.succ (X (a i.succ))))
      rw [Function.update_of_ne (Fin.succ_ne_zero i).symm, Fin.tail_update_succ]
      rfl

/-- Cast away the harmless leading zero in the unary Gerstenhaber bracket arity. -/
theorem curriedBracket_unary_eq_post_sub_insert (n : ℕ) (X : Unary R A)
    (F : Curried R A (n + 1)) :
    curriedCongr (Nat.zero_add (n + 1)) (curriedBracket 0 n X F) =
      curriedPost (n + 1) X F - curriedPreLie 1 n F X := by
  rw [curriedBracket, map_sub, map_smul, curriedPreLie_zero,
    curriedInsertHead_outer_unary]
  simp only [Nat.zero_mul, pow_zero, one_smul]
  apply congrArg (fun Z => curriedPost (n + 1) X F - Z)
  exact (curriedCongr_trans (R := R) (A := A)
    (congrArg (· + 1) (Nat.add_comm n 0)) (Nat.zero_add (n + 1))
      (curriedPreLie 1 n F X)).trans (curriedCongr_self _ _)

/-- The cochain action of a unary linear map, built from the actual insertion sum. -/
def cochainUnaryAction (n : ℕ) (X : Unary R A) (F : Cochain R A (n + 1)) : Cochain R A (n + 1) :=
  (cochainCurriedEquiv R A (n + 1)).symm
    (curriedPost (n + 1) X (cochainCurriedEquiv R A (n + 1) F) -
      curriedPreLie 1 n (cochainCurriedEquiv R A (n + 1) F) X)

theorem cochainUnaryAction_apply (n : ℕ) (X : Unary R A) (F : Cochain R A (n + 1))
    (a : Fin (n + 1) → A) :
    cochainUnaryAction n X F a = X (F a) - ∑ i, F (Function.update a i (X (a i))) := by
  rw [cochainUnaryAction,
    cochainCurriedEquiv_symm_apply (R := R) (A := A) (n + 1), curriedEval_sub,
    curriedEval_post, curriedPreLie_unary_eval, curriedEval_equiv]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  exact curriedEval_equiv (n + 1) F _

theorem cochainUnaryAction_smul (n : ℕ) (X : Unary R A) (r : R) (F : Cochain R A (n + 1)) :
    cochainUnaryAction n X (r • F) = r • cochainUnaryAction n X F := by
  apply MultilinearMap.ext
  intro a
  rw [cochainUnaryAction_apply]
  change X (r • F a) - ∑ i, r • F (Function.update a i (X (a i))) = _
  rw [map_smul, ← Finset.smul_sum, ← smul_sub]
  change r • (X (F a) - ∑ i, F (Function.update a i (X (a i)))) = _
  rw [← cochainUnaryAction_apply]
  rfl

/-- The ordinary unary action preserves the alternating permutation rule. -/
theorem cochainUnaryAction_alternating_perm (n : ℕ) (X : Unary R A)
    (F : A [⋀^Fin (n + 1)]→ₗ[R] A) (σ : Equiv.Perm (Fin (n + 1))) (a : Fin (n + 1) → A) :
    cochainUnaryAction n X F.toMultilinearMap (a ∘ σ) =
      Equiv.Perm.sign σ • cochainUnaryAction n X F.toMultilinearMap a := by
  have hupd (i : Fin (n + 1)) :
      F (Function.update (a ∘ σ) i (X (a (σ i)))) =
        Equiv.Perm.sign σ • F (Function.update a (σ i) (X (a (σ i)))) := by
    rw [← Function.update_comp_eq_of_injective a σ.injective i (X (a (σ i)))]
    exact F.map_perm _ σ
  have hsum : (∑ i, F (Function.update (a ∘ σ) i (X (a (σ i))))) =
      Equiv.Perm.sign σ • ∑ i, F (Function.update a i (X (a i))) := by
    calc
      _ = ∑ i, Equiv.Perm.sign σ • F (Function.update a (σ i) (X (a (σ i)))) :=
        Finset.sum_congr rfl (fun i _ => hupd i)
      _ = Equiv.Perm.sign σ • ∑ i, F (Function.update a (σ i) (X (a (σ i)))) :=
        Finset.smul_sum.symm
      _ = _ := congrArg (fun z => Equiv.Perm.sign σ • z)
        (Equiv.sum_comp σ (fun i => F (Function.update a i (X (a i)))))
  rw [cochainUnaryAction_apply, cochainUnaryAction_apply]
  change X (F (a ∘ σ)) - ∑ i, F (Function.update (a ∘ σ) i (X (a (σ i)))) = _
  rw [F.map_perm, hsum]
  simp only [Units.smul_def, map_zsmul, zsmul_sub]
  rfl

end LinearAction

namespace SignedDGLA

variable {R : Type*} [CommRing R] (D : SignedDGLA R)

private theorem d_congr {p q : ℤ} (h : p = q) (f : D.Obj p) :
    D.d q (gradedModuleCongr R D.complex.X h f) =
      gradedModuleCongr R D.complex.X (congrArg (· + 1) h) (D.d p f) := by
  subst q
  rfl

theorem d_zeroAction_eq_zero (p : ℤ) (X : D.Obj 0) (F : D.Obj p)
    (hX : D.d 0 X = 0) (hF : D.d p F = 0) : D.d p (D.zeroAction p X F) = 0 := by
  change D.d p (gradedModuleCongr R D.complex.X (zero_add p) (D.bracket 0 p X F)) = 0
  rw [d_congr, D.bracket_closed 0 p X F hX hF, map_zero]

end SignedDGLA

section Polynomial

variable {K : Type*} [Field K] [CharZero K] {d : ℕ}

/-- Full antisymmetrization cancels the HKR factorial in the vector-field action. -/
theorem alternatingEvaluation_cochainUnaryAction (n : ℕ) (X : Unary K (PolynomialFunctions K d))
    (F : Multiderivation K (PolynomialFunctions K d) (n + 1))
    (a : Fin (n + 1) → PolynomialFunctions K d) :
    alternatingEvaluation (cochainUnaryAction n X (Multiderivation.toCochain F)) a =
      X (F a) - ∑ i, F (Function.update a i (X (a i))) := by
  rw [alternatingEvaluation_apply]
  have hterm (σ : Equiv.Perm (Fin (n + 1))) :
      Equiv.Perm.sign σ • cochainUnaryAction n X (Multiderivation.toCochain F) (fun i => a (σ i)) =
        ((n + 1).factorial : K)⁻¹ • (X (F a) - ∑ i, F (Function.update a i (X (a i)))) := by
    change Equiv.Perm.sign σ •
      cochainUnaryAction n X (((n + 1).factorial : K)⁻¹ • F.val.toMultilinearMap) (a ∘ σ) = _
    rw [cochainUnaryAction_smul]
    change Equiv.Perm.sign σ • (((n + 1).factorial : K)⁻¹ •
      cochainUnaryAction n X F.val.toMultilinearMap (a ∘ σ)) = _
    rw [cochainUnaryAction_alternating_perm, smul_comm (Equiv.Perm.sign σ),
      smul_smul, Int.units_mul_self, one_smul, cochainUnaryAction_apply]
    rfl
  rw [Finset.sum_congr rfl (fun σ _ => hterm σ)]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul K, smul_smul,
    mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)), one_smul]

omit [CharZero K] in
private theorem hochschild_zeroAction_eq_cochainUnaryAction (n : ℕ)
    (X : Unary K (PolynomialFunctions K d)) (F : Cochain K (PolynomialFunctions K d) (n + 1)) :
    (hochschildDGLA (LinearMap.mul K (PolynomialFunctions K d)) mul_assoc).zeroAction n X
      (cochainCurriedEquiv K (PolynomialFunctions K d) (n + 1) F) =
      cochainCurriedEquiv K (PolynomialFunctions K d) (n + 1) (cochainUnaryAction n X F) := by
  calc
    _ = curriedCongr (Nat.zero_add (n + 1))
        (curriedBracket 0 n X (cochainCurriedEquiv K (PolynomialFunctions K d) (n + 1) F)) := by
      exact fullCochainCongr_nat (R := K) (A := PolynomialFunctions K d)
        (m := 0 + n) (n := n) (congrArg Int.ofNat (Nat.zero_add n)) _
    _ = curriedPost (n + 1) X (cochainCurriedEquiv K (PolynomialFunctions K d) (n + 1) F) -
        curriedPreLie 1 n (cochainCurriedEquiv K (PolynomialFunctions K d) (n + 1) F) X :=
      curriedBracket_unary_eq_post_sub_insert n X _
    _ = _ := by rw [cochainUnaryAction, LinearEquiv.apply_symm_apply]

/-- The genuine degree-zero DGLA action with its integer-degree transport resolved. -/
def schoutenVectorAction (n : ℕ) (X : Multiderivation K (PolynomialFunctions K d) 1)
    (F : Multiderivation K (PolynomialFunctions K d) (n + 1)) :
    Multiderivation K (PolynomialFunctions K d) (n + 1) :=
  (polynomialSchoutenDGLA K d).zeroAction (n : ℤ) X F

theorem schoutenVectorAction_eq_fromCochain (n : ℕ)
    (X : Multiderivation K (PolynomialFunctions K d) 1)
    (F : Multiderivation K (PolynomialFunctions K d) (n + 1)) :
    schoutenVectorAction n X F = Multiderivation.fromCochain
      (cochainUnaryAction n (Multiderivation.oneEquiv X).toLinearMap (Multiderivation.toCochain F)) := by
  change gradedModuleCongr K (fullPolyvectorObj K d) (zero_add (n : ℤ))
    (fullPolyvectorProjection K d (0 + n)
      (fullBracket 0 n (fullPolyvectorInclusion K d 0 X) (fullPolyvectorInclusion K d n F))) = _
  rw [← gradedLinearMap_congr]
  rw [fullPolyvectorInclusion_zero]
  change fullPolyvectorProjection K d n
    ((hochschildDGLA (LinearMap.mul K (PolynomialFunctions K d)) mul_assoc).zeroAction n
      (Multiderivation.oneEquiv X).toLinearMap
      (cochainCurriedEquiv K (PolynomialFunctions K d) (n + 1) (Multiderivation.toCochain F))) = _
  rw [hochschild_zeroAction_eq_cochainUnaryAction]
  change Multiderivation.fromCochain
    ((cochainCurriedEquiv K (PolynomialFunctions K d) (n + 1)).symm
      (cochainCurriedEquiv K (PolynomialFunctions K d) (n + 1) _)) = _
  rw [LinearEquiv.symm_apply_apply]

theorem cochainUnaryAction_toCochain_closed (n : ℕ)
    (X : Multiderivation K (PolynomialFunctions K d) 1)
    (F : Multiderivation K (PolynomialFunctions K d) (n + 1)) :
    barDifferential (LinearMap.mul K (PolynomialFunctions K d)) (n + 1)
      (cochainUnaryAction n (Multiderivation.oneEquiv X).toLinearMap (Multiderivation.toCochain F)) = 0 := by
  let D := hochschildDGLA (LinearMap.mul K (PolynomialFunctions K d)) mul_assoc
  have hc := D.d_zeroAction_eq_zero (n : ℤ)
    (fullPolyvectorInclusion K d 0 X) (fullPolyvectorInclusion K d n F)
    ((fullPolyvectorModel K d).closed 0 X) ((fullPolyvectorModel K d).closed n F)
  change ((fullComplex (LinearMap.mul K (PolynomialFunctions K d)) mul_assoc).d n (n + 1)).hom
    (D.zeroAction n (fullPolyvectorInclusion K d 0 X) (fullPolyvectorInclusion K d n F)) = 0 at hc
  rw [fullComplex_d, fullPolyvectorInclusion_zero] at hc
  change curriedDifferential (LinearMap.mul K (PolynomialFunctions K d)) n
    (D.zeroAction n (Multiderivation.oneEquiv X).toLinearMap
      (cochainCurriedEquiv K (PolynomialFunctions K d) (n + 1) (Multiderivation.toCochain F))) = 0 at hc
  rw [hochschild_zeroAction_eq_cochainUnaryAction] at hc
  have he := congrArg (cochainCurriedEquiv K (PolynomialFunctions K d) (n + 1 + 1)).symm hc
  rw [uncurried_curriedDifferential, LinearEquiv.symm_apply_apply, map_zero] at he
  exact (smul_eq_zero.mp he).resolve_left (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))

/-- The Schouten action is the actual Lie derivative in every positive arity. -/
theorem schoutenVectorAction_apply (n : ℕ)
    (X : Multiderivation K (PolynomialFunctions K d) 1)
    (F : Multiderivation K (PolynomialFunctions K d) (n + 1))
    (a : Fin (n + 1) → PolynomialFunctions K d) :
    schoutenVectorAction n X F a =
      (Multiderivation.oneEquiv X) (F a) -
        ∑ i, F (Function.update a i ((Multiderivation.oneEquiv X) (a i))) := by
  rw [schoutenVectorAction_eq_fromCochain,
    Multiderivation.fromCochain_apply_of_closed _ (cochainUnaryAction_toCochain_closed n X F),
    alternatingEvaluation_cochainUnaryAction]
  rfl

/-- The retained degree-minus-one component has the usual vector-field action on functions. -/
theorem schoutenVectorAction_function (X : Multiderivation K (PolynomialFunctions K d) 1)
    (f : PolynomialFunctions K d) :
    (polynomialSchoutenDGLA K d).zeroAction (-1) X f = (Multiderivation.oneEquiv X) f :=
  schoutenBracket_vector_function X f

/-- In arity two the general formula is precisely the familiar three-term Lie derivative. -/
theorem schoutenVectorAction_bivector_apply
    (X : Multiderivation K (PolynomialFunctions K d) 1)
    (F : Multiderivation K (PolynomialFunctions K d) 2) (a b : PolynomialFunctions K d) :
    schoutenVectorAction 1 X F (Fin.cons a (Fin.cons b Fin.elim0)) =
      (Multiderivation.oneEquiv X) (F (Fin.cons a (Fin.cons b Fin.elim0))) -
        F (Fin.cons ((Multiderivation.oneEquiv X) a) (Fin.cons b Fin.elim0)) -
        F (Fin.cons a (Fin.cons ((Multiderivation.oneEquiv X) b) Fin.elim0)) := by
  rw [schoutenVectorAction_apply, Fin.sum_univ_two]
  have hu : Function.update
      (Fin.cons a (Fin.cons b Fin.elim0) : Fin 2 → PolynomialFunctions K d) (1 : Fin 2)
        ((Multiderivation.oneEquiv X) b) =
      (Fin.cons a (Fin.cons ((Multiderivation.oneEquiv X) b) Fin.elim0) :
        Fin 2 → PolynomialFunctions K d) := by
    change Function.update (Fin.cons a (Fin.cons b Fin.elim0) : Fin 2 → PolynomialFunctions K d)
      (0 : Fin 1).succ _ = _
    rw [← Fin.cons_update, Fin.update_cons_zero]
  simp only [Fin.cons_zero, Fin.cons_one, Fin.update_cons_zero, hu]
  abel

/-- Raw bivector evaluation, with no HKR factor, in the existing binary-cochain representation. -/
def rawBivector (F : Multiderivation K (PolynomialFunctions K d) 2) :
    Binary K (PolynomialFunctions K d) :=
  cochainTwoEquiv K (PolynomialFunctions K d) F.val.toMultilinearMap

omit [CharZero K] in
theorem rawBivector_apply (F : Multiderivation K (PolynomialFunctions K d) 2)
    (a b : PolynomialFunctions K d) : rawBivector F a b = F (Fin.cons a (Fin.cons b Fin.elim0)) := by
  have h := cochainTwoEquiv_symm_apply K (PolynomialFunctions K d)
    (cochainTwoEquiv K (PolynomialFunctions K d) F.val.toMultilinearMap)
    (Fin.cons a (Fin.cons b Fin.elim0))
  rw [LinearEquiv.symm_apply_apply] at h
  exact h.symm

def rawBivectorLinearMap : Multiderivation K (PolynomialFunctions K d) 2 →ₗ[K]
    Binary K (PolynomialFunctions K d) where
  toFun := rawBivector
  map_add' F G := (cochainTwoEquiv K (PolynomialFunctions K d)).map_add F.val.toMultilinearMap G.val.toMultilinearMap
  map_smul' c F := (cochainTwoEquiv K (PolynomialFunctions K d)).map_smul c F.val.toMultilinearMap

/-- The source Schouten action agrees with the exact binary action used by conjugation. -/
theorem rawBivector_schoutenVectorAction
    (X : Multiderivation K (PolynomialFunctions K d) 1)
    (F : Multiderivation K (PolynomialFunctions K d) 2) :
    rawBivector (schoutenVectorAction 1 X F) =
      unaryAction (Multiderivation.oneEquiv X).toLinearMap (rawBivector F) := by
  apply LinearMap.ext
  intro a
  apply LinearMap.ext
  intro b
  rw [rawBivector_apply, unaryAction_apply, rawBivector_apply, rawBivector_apply, rawBivector_apply]
  exact schoutenVectorAction_bivector_apply X F a b

end Polynomial

end EnvelopingIsomorphism.Deformation
