import EnvelopingIsomorphism.Deformation.MixedGraphCorrectionMultilinear
import EnvelopingIsomorphism.Deformation.MixedGraphAveraging

/-! Binary-output adapter for the genuine two-odd multilinear correction profile. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

namespace EnvelopingIsomorphism.Deformation.MixedGraphCorrectionBinary

open MixedGraphProfileCarrier MixedGraphCorrectionProfiles MixedGraphCorrectionMultilinear
open GraphCoefficientProfiles
open scoped BigOperators Classical

variable {k : Type*} [Field k] [CharZero k] {n d : ℕ}

/-- The genuine cochain-two equivalence applied after the independent vector input. -/
def mapBinary {l : ℕ} : ProfileMap (k := k) (d := d) l →ₗ[k] MixedGraphAveraging.MixedMap k d l where
  toFun F := (LinearMap.llcomp k _ _ _ (cochainTwoEquiv k (MvPolynomial (Fin d) k)).toLinearMap).compMultilinearMap F
  map_add' F G := by ext R X f g; rfl
  map_smul' r F := by ext R X f g; rfl

@[simp] theorem mapBinary_operator {l : ℕ} (Γ : VectorGraph l 2) :
    mapBinary (operator (k := k) (d := d) Γ) = binaryValue Γ := rfl

theorem mapBinary_symmetrize {l : ℕ} (F : ProfileMap (k := k) (d := d) l) :
    mapBinary (MixedGraphCorrectionMultilinear.symmetrize F) =
      MixedGraphAveraging.symmetrize (mapBinary F) := by
  apply MultilinearMap.ext
  intro R
  apply LinearMap.ext
  intro X
  simp only [MixedGraphCorrectionMultilinear.symmetrize_apply, MixedGraphAveraging.symmetrize_apply]
  change cochainTwoEquiv k _ ((MixedGraphCorrectionMultilinear.symmetrize F R) X) = _
  rw [MixedGraphCorrectionMultilinear.symmetrize_apply]
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  rfl

/-- This is exactly the mixed scalar averaging API used by the path relation assembly. -/
theorem evaluation_symmetrized_correctionProfile_binary (w : CorrectionGraph n → k) :
    evaluation (MixedGraphAveraging.symmetrizedBinaryValue (k := k) (d := d)) (correctionProfile w) =
      MixedGraphAveraging.symmetrize (mapBinary (groupedCorrectionMap w)) := by
  rw [← mapBinary_symmetrize, ← evaluation_symmetrized_correctionProfile_grouped]
  simp only [evaluation_apply, map_sum, map_smul, mapBinary_symmetrize,
    mapBinary_operator, MixedGraphAveraging.symmetrizedBinaryValue]

/-- The independent correction operation remains linear in both X and Q after
conversion to the actual binary target space. -/
def correctionSource (w : CorrectionGraph n → k) :
    MultilinearMap k (fun _ : Fin n => Bivector (k := k) (d := d))
      (Vector (k := k) (d := d) →ₗ[k] Trivector (k := k) (d := d) →ₗ[k] Binary k (MvPolynomial (Fin d) k)) :=
  (LinearMap.llcomp k _ _ _ (LinearMap.llcomp k _ _ _
    (cochainTwoEquiv k (MvPolynomial (Fin d) k)).toLinearMap)).compMultilinearMap (correctionFamily w)

/-- Exact source bracket grouping for arbitrary independent inputs, with one-half
inside the separately linear curvature argument and the two-odd signs in the family. -/
theorem groupedCorrectionMap_source (w : CorrectionGraph n → k)
    (R : Fin (n + 2) → Bivector (k := k) (d := d)) (X : Vector (k := k) (d := d)) :
    mapBinary (groupedCorrectionMap w) R X = correctionSource w (fun j => R (Fin.castAdd 2 j)) X
      ((1 / 2 : k) • (show Trivector (k := k) (d := d) from
        schoutenBracket k d 1 1 (R (Fin.natAdd n 0)) (R (Fin.natAdd n 1)))) :=
  congrArg (cochainTwoEquiv k (MvPolynomial (Fin d) k)) (groupedCorrectionMap_apply_family w R X)

end EnvelopingIsomorphism.Deformation.MixedGraphCorrectionBinary
