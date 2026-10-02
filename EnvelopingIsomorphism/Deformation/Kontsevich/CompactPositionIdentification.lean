import EnvelopingIsomorphism.Deformation.Kontsevich.Compactification
import EnvelopingIsomorphism.Deformation.Kontsevich.ReferenceNormIdentification
import EnvelopingIsomorphism.Deformation.Kontsevich.DirectionRatioInvariant
import EnvelopingIsomorphism.Deformation.Kontsevich.OnePointRadialIdentification
import Mathlib.Topology.DenseEmbedding

/-! Recover positions from full doubled directions and triple ratios.
The reference pair is the normalized anchor and its reflected point, of distance two.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich

open Configuration ComplexConjugate Topology

variable {n m : ℕ}

/-- The source is the reflected anchor, and the second reference target is the anchor itself.
The two targets may coincide, as allowed by the native triple-coordinate type. -/
def positionIdentificationTriple (i : Fin n) (v : Fin n ⊕ Fin m) : DoubledTriple n m :=
  ⟨(Sum.inr i, Sum.inl v, Sum.inl (Sum.inl i)), by simp⟩

theorem pairDifference_normalized_anchor {i : Fin n} (c : Normalized i m)
    (v : Fin n ⊕ Fin m) :
    c.val.pairDifference (harmonicDenominatorPair i v) = c.val.vertexPoint v + Complex.I := by
  change c.val.vertexPoint v - conj (c.val.interior i : ℂ) = _
  rw [c.property]
  simp

theorem tripleDistanceRatio_normalized_anchor {i : Fin n} (c : Normalized i m)
    (v : Fin n ⊕ Fin m) :
    (c.val.tripleDistanceRatio (positionIdentificationTriple i v) : ℝ) =
      referenceNormRatio 2 (c.val.vertexPoint v + Complex.I) := by
  change ‖c.val.vertexPoint v - conj (c.val.interior i : ℂ)‖ /
    (‖c.val.vertexPoint v - conj (c.val.interior i : ℂ)‖ +
      ‖(c.val.interior i : ℂ) - conj (c.val.interior i : ℂ)‖) = _
  rw [c.property]
  have hnorm : ‖Complex.I + Complex.I‖ = (2 : ℝ) := by
    rw [← two_mul, norm_mul]
    simp
  simp only [UpperHalfPlane.coe_I, Complex.conj_I, sub_neg_eq_add, hnorm]
  rfl

theorem positionIdentificationRatio_lt_one {i : Fin n} (c : Normalized i m)
    (v : Fin n ⊕ Fin m) : (c.val.tripleDistanceRatio (positionIdentificationTriple i v) : ℝ) < 1 := by
  rw [tripleDistanceRatio_normalized_anchor]
  exact referenceNormRatio_lt_one (by norm_num) _

/-- Exact finite reconstruction from entries already stored by the compactification encoder. -/
theorem recoverPosition_normalized {i : Fin n} (c : Normalized i m) (v : Fin n ⊕ Fin m) :
    (2 : ℂ) * recoverRelativePosition
      (complexPhase (c.val.pairDifference (harmonicDenominatorPair i v)))
      (c.val.tripleDistanceRatio (positionIdentificationTriple i v) : ℝ) - Complex.I =
        c.val.vertexPoint v := by
  rw [pairDifference_normalized_anchor, tripleDistanceRatio_normalized_anchor]
  have h := recoverRelativePosition_referenceNormRatio (by norm_num : (0 : ℝ) < 2)
    (c.val.vertexPoint v + Complex.I)
  simpa using congrArg (fun z : ℂ ↦ z - Complex.I) h

/-- An actual continuous position-valued function of the full direction/ratio data.
Ratio one is sent to infinity by the genuine radial identification map. -/
def compactPositionFromDR (i : Fin n) (v : Fin n ⊕ Fin m) (x : DRData n m) : OnePoint ℂ :=
  onePointRadialIdentificationSub 2 Complex.I
    (x.1 (harmonicDenominatorPair i v), x.2 (positionIdentificationTriple i v))

@[fun_prop] theorem continuous_compactPositionFromDR (i : Fin n) (v : Fin n ⊕ Fin m) :
    Continuous (compactPositionFromDR i v) := by
  apply (continuous_onePointRadialIdentificationSub (by norm_num : (0 : ℝ) < 2) Complex.I).comp
  exact ((continuous_apply (harmonicDenominatorPair i v)).comp continuous_fst).prodMk
    ((continuous_apply (positionIdentificationTriple i v)).comp continuous_snd)

/-- The continuous reconstruction equals the stored finite position on every original input. -/
theorem compactPositionFromDR_normalized {i : Fin n} (c : Normalized i m)
    (v : Fin n ⊕ Fin m) :
    compactPositionFromDR i v (normalizedDirectionRatios c) =
      (c.val.vertexPoint v : OnePoint ℂ) := by
  change onePointRadialIdentificationSub 2 Complex.I
    (complexPhase (c.val.pairDifference (harmonicDenominatorPair i v)),
      c.val.tripleDistanceRatio (positionIdentificationTriple i v)) = _
  rw [pairDifference_normalized_anchor]
  have hr : c.val.tripleDistanceRatio (positionIdentificationTriple i v) =
      referenceNormRatioIcc (by norm_num : (0 : ℝ) < 2) (c.val.vertexPoint v + Complex.I) :=
    Subtype.ext (tripleDistanceRatio_normalized_anchor c v)
  rw [hr, onePointRadialIdentificationSub_phase_ratio]
  simp

/-- Equality extends to every boundary point, by continuity and the actual dense configuration image. -/
theorem compactification_position_identification (i : Fin n) (v : Fin n ⊕ Fin m)
    (x : Compactification i m) :
    compactPositionFromDR i v (projectDR x.val) = x.val.1 v := by
  have heq : (fun x : Compactification i m ↦ compactPositionFromDR i v (projectDR x.val)) =
      (fun x : Compactification i m ↦ x.val.1 v) := by
    apply (denseRange_compactificationEmbedding i).equalizer
    · exact (continuous_compactPositionFromDR i v).comp
        (continuous_projectDR.comp continuous_subtype_val)
    · fun_prop
    · funext c
      exact compactPositionFromDR_normalized c v
  exact congrFun heq x

/-- Forgetting the compactified positions loses no information on the actual compactification.
This uses all doubled direction and triple-ratio coordinates, not just harmonic angles. -/
theorem projectDR_injective_on_compactification (i : Fin n) :
    Function.Injective (fun x : Compactification i m ↦ projectDR x.val) := by
  intro x y h
  apply Subtype.ext
  apply Prod.ext
  · funext v
    rw [← compactification_position_identification i v x, ← compactification_position_identification i v y]
    exact congrArg (compactPositionFromDR i v) h
  · exact h

end EnvelopingIsomorphism.Deformation.Kontsevich
