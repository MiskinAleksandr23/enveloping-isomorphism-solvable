import EnvelopingIsomorphism.Deformation.Kontsevich.GeometricWeights

/-!
# Vanishing of raw graph forms with loops or repeated directed edges

The raw `GraphForms.Edge` type deliberately allows these degeneracies. The
results apply before an admissible graph structure is supplied, as needed for
quotient graphs arising from contractions. They do not assert a contraction or
Stokes identity, or a limiting value for an angle form at a collision.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich

theorem harmonicRatio_self (p : ℂ) : harmonicRatio p p = 0 := by
  simp [harmonicRatio]

/-- The repository's total harmonic form is zero at an identical endpoint pair.
This follows from its actual zero angular coefficient at ratio zero. -/
theorem harmonicAngleForm_self (p : ℂ) : harmonicAngleForm (p, p) = 0 := by
  ext v
  simp [harmonicAngleForm_apply, harmonicRatio_self]

namespace GraphForms

variable {n m : ℕ}

theorem edgeRatio_eq_zero_of_selfLoop (e : Edge n m)
    (he : e.target = Sum.inl e.source) :
    (fun x : Coordinates n m => harmonicRatio (edgeMap e x).1 (edgeMap e x).2) = 0 := by
  funext x
  simp [edgeMap, vertexPoint, he, harmonicRatio_self]

theorem edgeForm_eq_zero_of_selfLoop (e : Edge n m)
    (he : e.target = Sum.inl e.source) (x : Coordinates n m) : edgeForm e x = 0 := by
  have hmap : edgeMap e x = (interiorPoint e.source x, interiorPoint e.source x) := by
    simp [edgeMap, vertexPoint, he]
  ext v
  simp [edgeForm, hmap, harmonicAngleForm_self]

theorem edgeLinear_eq_zero_of_selfLoop (e : Edge n m)
    (he : e.target = Sum.inl e.source) (x : Coordinates n m) : edgeLinear e x = 0 := by
  apply ContinuousLinearMap.ext
  intro v
  rw [edgeLinear_apply, edgeForm_eq_zero_of_selfLoop e he x]
  rfl

/-- A loop supplies a zero column in the determinant product, in every degree. -/
theorem topForm_eq_zero_of_selfLoop {r : ℕ} (edges : Fin r → Edge n m)
    (a : Fin r) (ha : (edges a).target = Sum.inl (edges a).source)
    (x : Coordinates n m) : topForm edges x = 0 := by
  ext v
  change topForm edges x v = 0
  rw [topForm_apply]
  apply Matrix.det_eq_zero_of_column_eq_zero a
  intro i
  rw [edgeForm_eq_zero_of_selfLoop (edges a) ha x]
  rfl

/-- Repeated directed edges supply equal determinant columns. -/
theorem topForm_eq_zero_of_duplicate {r : ℕ} (edges : Fin r → Edge n m)
    (a b : Fin r) (hab : a ≠ b) (he : edges a = edges b)
    (x : Coordinates n m) : topForm edges x = 0 := by
  ext v
  change topForm edges x v = 0
  rw [topForm_apply]
  apply Matrix.det_zero_of_column_eq hab
  intro i
  rw [he]

theorem topForm_eq_zero_of_same_endpoints {r : ℕ} (edges : Fin r → Edge n m)
    (a b : Fin r) (hab : a ≠ b)
    (hs : (edges a).source = (edges b).source)
    (ht : (edges a).target = (edges b).target)
    (x : Coordinates n m) : topForm edges x = 0 := by
  apply topForm_eq_zero_of_duplicate edges a b hab _ x
  cases hea : edges a
  cases heb : edges b
  simp_all

theorem topDensity_eq_zero_of_selfLoop
    (edges : Fin (dimension n m) → Edge n m) (a : Fin (dimension n m))
    (ha : (edges a).target = Sum.inl (edges a).source) : topDensity edges = 0 := by
  funext x
  simp [topDensity, topForm_eq_zero_of_selfLoop edges a ha x]

theorem topDensity_eq_zero_of_duplicate
    (edges : Fin (dimension n m) → Edge n m) (a b : Fin (dimension n m))
    (hab : a ≠ b) (he : edges a = edges b) : topDensity edges = 0 := by
  funext x
  simp [topDensity, topForm_eq_zero_of_duplicate edges a b hab he x]

theorem integral_topDensity_eq_zero_of_selfLoop
    (edges : Fin (dimension n m) → Edge n m) (a : Fin (dimension n m))
    (ha : (edges a).target = Sum.inl (edges a).source)
    (s : Set (Coordinates n m)) (μ : MeasureTheory.Measure (Coordinates n m)) :
    (∫ x in s, topDensity edges x ∂μ) = 0 := by
  simp only [topDensity_eq_zero_of_selfLoop edges a ha, Pi.zero_apply, MeasureTheory.integral_zero]

theorem integral_topDensity_eq_zero_of_duplicate
    (edges : Fin (dimension n m) → Edge n m) (a b : Fin (dimension n m))
    (hab : a ≠ b) (he : edges a = edges b)
    (s : Set (Coordinates n m)) (μ : MeasureTheory.Measure (Coordinates n m)) :
    (∫ x in s, topDensity edges x ∂μ) = 0 := by
  simp only [topDensity_eq_zero_of_duplicate edges a b hab he,
    Pi.zero_apply, MeasureTheory.integral_zero]

end GraphForms

namespace GeometricWeights

open GraphForms

variable {n m : ℕ}

theorem realDensity_eq_zero_of_selfLoop
    (edges : Fin (dimension n m) → Edge n m) (a : Fin (dimension n m))
    (ha : (edges a).target = Sum.inl (edges a).source) : realDensity edges = 0 := by
  funext x
  simp [realDensity, topDensity_eq_zero_of_selfLoop edges a ha]

theorem realDensity_eq_zero_of_duplicate
    (edges : Fin (dimension n m) → Edge n m) (a b : Fin (dimension n m))
    (hab : a ≠ b) (he : edges a = edges b) : realDensity edges = 0 := by
  funext x
  simp [realDensity, topDensity_eq_zero_of_duplicate edges a b hab he]

theorem rawIntegral_eq_zero_of_selfLoop
    (edges : Fin (dimension n m) → Edge n m) (a : Fin (dimension n m))
    (ha : (edges a).target = Sum.inl (edges a).source) : rawIntegral edges = 0 := by
  simp [rawIntegral, realDensity_eq_zero_of_selfLoop edges a ha]

theorem rawIntegral_eq_zero_of_duplicate
    (edges : Fin (dimension n m) → Edge n m) (a b : Fin (dimension n m))
    (hab : a ≠ b) (he : edges a = edges b) : rawIntegral edges = 0 := by
  simp [rawIntegral, realDensity_eq_zero_of_duplicate edges a b hab he]

theorem absolutelyIntegrable_of_selfLoop
    (edges : Fin (dimension n m) → Edge n m) (a : Fin (dimension n m))
    (ha : (edges a).target = Sum.inl (edges a).source) : AbsolutelyIntegrable edges := by
  rw [AbsolutelyIntegrable, realDensity_eq_zero_of_selfLoop edges a ha]
  exact MeasureTheory.integrableOn_zero

theorem absolutelyIntegrable_of_duplicate
    (edges : Fin (dimension n m) → Edge n m) (a b : Fin (dimension n m))
    (hab : a ≠ b) (he : edges a = edges b) : AbsolutelyIntegrable edges := by
  rw [AbsolutelyIntegrable, realDensity_eq_zero_of_duplicate edges a b hab he]
  exact MeasureTheory.integrableOn_zero

/-- The same actual geometric normalization used by `geometricWeight`, now
applied to a raw edge list which may contain a loop. -/
theorem normalized_rawIntegral_eq_zero_of_selfLoop (q : Fin (n + 1) → ℕ)
    (edges : Fin (dimension n m) → Edge n m) (a : Fin (dimension n m))
    (ha : (edges a).target = Sum.inl (edges a).source) :
    outgoingFactor q * ((2 * Real.pi) ^ dimension n m)⁻¹ * rawIntegral edges = 0 := by
  rw [rawIntegral_eq_zero_of_selfLoop edges a ha, mul_zero]

/-- A duplicate directed edge likewise kills the actually normalized integral. -/
theorem normalized_rawIntegral_eq_zero_of_duplicate (q : Fin (n + 1) → ℕ)
    (edges : Fin (dimension n m) → Edge n m) (a b : Fin (dimension n m))
    (hab : a ≠ b) (he : edges a = edges b) :
    outgoingFactor q * ((2 * Real.pi) ^ dimension n m)⁻¹ * rawIntegral edges = 0 := by
  rw [rawIntegral_eq_zero_of_duplicate edges a b hab he, mul_zero]

end GeometricWeights

end EnvelopingIsomorphism.Deformation.Kontsevich
