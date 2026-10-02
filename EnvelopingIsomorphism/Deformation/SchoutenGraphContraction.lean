import EnvelopingIsomorphism.Deformation.SchoutenJacobi
import EnvelopingIsomorphism.Deformation.MultiderivationCoordinateExpansion

/-! Raw coordinate formulas for the two-vertex source contractions needed by
the graph identities. No outgoing factorial or circle-integral factor is
absorbed in these formulas. The signed DGLA degree is arity minus one. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.SchoutenGraphContraction

set_option backward.isDefEq.respectTransparency false

open MvPolynomial
open scoped BigOperators

universe u
variable {K : Type u} [Field K] [CharZero K] {d : ℕ}

/-- Raw vector-field coordinate, without any graph normalization. -/
def vectorComponent (X : Multiderivation K (PolynomialFunctions K d) 1) (i : Fin d) :
    PolynomialFunctions K d := (Multiderivation.oneEquiv X) (MvPolynomial.X i)

/-- Raw bivector coordinate, without the HKR factor one half. -/
def bivectorComponent (F : Multiderivation K (PolynomialFunctions K d) 2) (i j : Fin d) :
    PolynomialFunctions K d := rawBivector F (MvPolynomial.X i) (MvPolynomial.X j)

/-- Raw trivector coordinate, without the HKR factor one sixth. -/
def trivectorComponent (F : Multiderivation K (PolynomialFunctions K d) 3) (i j k : Fin d) :
    PolynomialFunctions K d := rawTrivector F (MvPolynomial.X i) (MvPolynomial.X j) (MvPolynomial.X k)

omit [CharZero K] in
theorem vectorComponent_apply (X : Multiderivation K (PolynomialFunctions K d) 1) (i : Fin d) :
    vectorComponent X i = X ![MvPolynomial.X i] := by
  have h := congrArg (fun Y : Multiderivation K (PolynomialFunctions K d) 1 ↦ Y ![MvPolynomial.X i])
    (Multiderivation.ofDerivation_oneEquiv X)
  exact h

omit [CharZero K] in
theorem bivectorComponent_apply (F : Multiderivation K (PolynomialFunctions K d) 2) (i j : Fin d) :
    bivectorComponent F i j = F ![MvPolynomial.X i, MvPolynomial.X j] :=
  rawBivector_apply F _ _

omit [CharZero K] in
theorem bivectorComponent_skew (F : Multiderivation K (PolynomialFunctions K d) 2) (i j : Fin d) :
    bivectorComponent F j i = -bivectorComponent F i j := rawBivector_skew F _ _

omit [CharZero K] in
theorem trivectorComponent_apply (F : Multiderivation K (PolynomialFunctions K d) 3) (i j k : Fin d) :
    trivectorComponent F i j k = F ![MvPolynomial.X i, MvPolynomial.X j, MvPolynomial.X k] :=
  rawTrivector_apply F _ _ _

omit [CharZero K] in
theorem vector_apply (X : Multiderivation K (PolynomialFunctions K d) 1) (p : PolynomialFunctions K d) :
    (Multiderivation.oneEquiv X) p = ∑ s : Fin d, vectorComponent X s * pderiv s p :=
  Multiderivation.derivation_apply_coordinate_expansion _ _

omit [CharZero K] in
theorem bivector_apply_left_coordinate (F : Multiderivation K (PolynomialFunctions K d) 2)
    (p : PolynomialFunctions K d) (j : Fin d) :
    rawBivector F p (MvPolynomial.X j) =
      ∑ s : Fin d, bivectorComponent F s j * pderiv s p := by
  let D := F.slotDerivation (0 : Fin 2) ![p, MvPolynomial.X j]
  have h := Multiderivation.derivation_apply_coordinate_expansion D p
  have hD (x : PolynomialFunctions K d) : D x = rawBivector F x (MvPolynomial.X j) := by
    rw [rawBivector_apply]
    change F (Function.update (![p, MvPolynomial.X j] : Fin 2 → PolynomialFunctions K d) 0 x) = _
    congr 1
    funext i
    fin_cases i <;> simp
  simpa only [hD, bivectorComponent] using h

omit [CharZero K] in
theorem bivector_apply_right_coordinate (F : Multiderivation K (PolynomialFunctions K d) 2)
    (i : Fin d) (p : PolynomialFunctions K d) :
    rawBivector F (MvPolynomial.X i) p =
      ∑ s : Fin d, bivectorComponent F i s * pderiv s p := by
  let D := F.slotDerivation (1 : Fin 2) ![MvPolynomial.X i, p]
  have h := Multiderivation.derivation_apply_coordinate_expansion D p
  have hD (x : PolynomialFunctions K d) : D x = rawBivector F (MvPolynomial.X i) x := by
    rw [rawBivector_apply]
    change F (Function.update (![MvPolynomial.X i, p] : Fin 2 → PolynomialFunctions K d) 1 x) = _
    congr 1
    funext j
    fin_cases j <;> simp
  simpa only [hD, bivectorComponent] using h

/-- A single directed internal edge from F to G, with the three outgoing legs
in the indicated cyclic order. It occurs with numerical coefficient one. -/
def bivectorJoin (F G : Multiderivation K (PolynomialFunctions K d) 2) (i j k : Fin d) :
    PolynomialFunctions K d := ∑ s : Fin d, bivectorComponent F s k * pderiv s (bivectorComponent G i j)

/-- The raw two-bivector bracket is six explicitly ordered one-edge contractions. -/
theorem bivector_bracket_coordinates
    (F G : Multiderivation K (PolynomialFunctions K d) 2) (i j k : Fin d) :
    trivectorComponent
        (show Multiderivation K (PolynomialFunctions K d) 3 from schoutenBracket K d 1 1 F G) i j k =
      bivectorJoin F G i j k + bivectorJoin F G j k i + bivectorJoin F G k i j +
        (bivectorJoin G F i j k + bivectorJoin G F j k i + bivectorJoin G F k i j) := by
  let B : Multiderivation K (PolynomialFunctions K d) 3 := schoutenBracket K d 1 1 F G
  calc
    trivectorComponent B i j k = B ![MvPolynomial.X i, MvPolynomial.X j, MvPolynomial.X k] :=
      trivectorComponent_apply B i j k
    _ = jacobiInsert (rawBivector F) (rawBivector G) (MvPolynomial.X i) (MvPolynomial.X j) (MvPolynomial.X k) +
        jacobiInsert (rawBivector G) (rawBivector F) (MvPolynomial.X i) (MvPolynomial.X j) (MvPolynomial.X k) :=
      schoutenBivectors_apply F G _ _ _
    _ = _ := by
      simp only [jacobiInsert_apply]
      change rawBivector F (bivectorComponent G i j) (MvPolynomial.X k) +
        rawBivector F (bivectorComponent G j k) (MvPolynomial.X i) +
        rawBivector F (bivectorComponent G k i) (MvPolynomial.X j) +
        (rawBivector G (bivectorComponent F i j) (MvPolynomial.X k) +
          rawBivector G (bivectorComponent F j k) (MvPolynomial.X i) +
          rawBivector G (bivectorComponent F k i) (MvPolynomial.X j)) = _
      rw [bivector_apply_left_coordinate F (bivectorComponent G i j) k,
        bivector_apply_left_coordinate F (bivectorComponent G j k) i,
        bivector_apply_left_coordinate F (bivectorComponent G k i) j,
        bivector_apply_left_coordinate G (bivectorComponent F i j) k,
        bivector_apply_left_coordinate G (bivectorComponent F j k) i,
        bivector_apply_left_coordinate G (bivectorComponent F k i) j]
      rfl

/-- The factor two for a repeated bivector is not hidden in any graph weight. -/
theorem bivector_square_coordinates (F : Multiderivation K (PolynomialFunctions K d) 2)
    (i j k : Fin d) :
    trivectorComponent
        (show Multiderivation K (PolynomialFunctions K d) 3 from schoutenBracket K d 1 1 F F) i j k =
      (2 : K) • (bivectorJoin F F i j k + bivectorJoin F F j k i + bivectorJoin F F k i j) := by
  rw [bivector_bracket_coordinates, two_smul]

/-- A vector source feeding a derivative into a bivector coefficient. -/
def vectorToBivector (X : Multiderivation K (PolynomialFunctions K d) 1)
    (F : Multiderivation K (PolynomialFunctions K d) 2) (i j : Fin d) : PolynomialFunctions K d :=
  ∑ s : Fin d, vectorComponent X s * pderiv s (bivectorComponent F i j)

/-- The two opposite directed-edge terms retain their individual minus signs. -/
def bivectorToVectorLeft (F : Multiderivation K (PolynomialFunctions K d) 2)
    (X : Multiderivation K (PolynomialFunctions K d) 1) (i j : Fin d) : PolynomialFunctions K d :=
  ∑ s : Fin d, bivectorComponent F s j * pderiv s (vectorComponent X i)

def bivectorToVectorRight (F : Multiderivation K (PolynomialFunctions K d) 2)
    (X : Multiderivation K (PolynomialFunctions K d) 1) (i j : Fin d) : PolynomialFunctions K d :=
  ∑ s : Fin d, bivectorComponent F i s * pderiv s (vectorComponent X j)

omit [CharZero K] in
theorem bivectorToVectorRight_eq_neg_swapped
    (F : Multiderivation K (PolynomialFunctions K d) 2)
    (X : Multiderivation K (PolynomialFunctions K d) 1) (i j : Fin d) :
    bivectorToVectorRight F X i j = -bivectorToVectorLeft F X j i := by
  rw [bivectorToVectorRight, bivectorToVectorLeft, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro s hs
  rw [bivectorComponent_skew F s i, neg_mul]

/-- The actual unsuspended [X,F] coefficient is output minus both input actions. -/
theorem vector_bivector_coordinates
    (X : Multiderivation K (PolynomialFunctions K d) 1)
    (F : Multiderivation K (PolynomialFunctions K d) 2) (i j : Fin d) :
    bivectorComponent (schoutenVectorAction 1 X F) i j =
      vectorToBivector X F i j - bivectorToVectorLeft F X i j - bivectorToVectorRight F X i j := by
  change rawBivector (schoutenVectorAction 1 X F) (MvPolynomial.X i) (MvPolynomial.X j) = _
  rw [rawBivector_schoutenVectorAction, unaryAction_apply]
  change (Multiderivation.oneEquiv X) (bivectorComponent F i j) -
    rawBivector F (vectorComponent X i) (MvPolynomial.X j) -
    rawBivector F (MvPolynomial.X i) (vectorComponent X j) = _
  rw [vector_apply X (bivectorComponent F i j),
    bivector_apply_left_coordinate F (vectorComponent X i) j,
    bivector_apply_right_coordinate F i (vectorComponent X j)]
  rfl

/-- With the internal edge placed first at its source, the three canonical
joined graphs have signs plus, minus, plus. -/
theorem vector_bivector_coordinates_canonical
    (X : Multiderivation K (PolynomialFunctions K d) 1)
    (F : Multiderivation K (PolynomialFunctions K d) 2) (i j : Fin d) :
    bivectorComponent (schoutenVectorAction 1 X F) i j =
      vectorToBivector X F i j - bivectorToVectorLeft F X i j + bivectorToVectorLeft F X j i := by
  rw [vector_bivector_coordinates, bivectorToVectorRight_eq_neg_swapped, sub_neg_eq_add]

end EnvelopingIsomorphism.Deformation.SchoutenGraphContraction
