import EnvelopingIsomorphism.Deformation.Kontsevich.AngleRatio

/-!
# The coordinate topology and doubled configuration points

The topology is the subspace topology of the actual complex vertex coordinates.
Adjoining one conjugate copy of every interior vertex gives a finite family of
distinct points suitable for direction and distance-ratio coordinates.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich

open ComplexConjugate Topology

namespace Configuration

variable {n m : ℕ}

theorem vertexCoordinates_injective :
    Function.Injective (vertexPoint : Configuration n m → (Fin n ⊕ Fin m) → ℂ) := by
  intro c d h
  apply ext
  · funext i
    exact UpperHalfPlane.ext (congrFun h (Sum.inl i))
  · funext j
    exact Complex.ofReal_injective (congrFun h (Sum.inr j))

instance instTopologicalSpace : TopologicalSpace (Configuration n m) :=
  TopologicalSpace.induced vertexPoint inferInstance

instance instNormalizedTopologicalSpace (i : Fin n) : TopologicalSpace (Normalized i m) :=
  inferInstanceAs (TopologicalSpace {c : Configuration n m // c.interior i = UpperHalfPlane.I})

theorem isEmbedding_vertexCoordinates :
    IsEmbedding (vertexPoint : Configuration n m → (Fin n ⊕ Fin m) → ℂ) :=
  vertexCoordinates_injective.isEmbedding_induced

@[fun_prop] theorem continuous_vertexCoordinates :
    Continuous (vertexPoint : Configuration n m → (Fin n ⊕ Fin m) → ℂ) :=
  isEmbedding_vertexCoordinates.continuous

@[fun_prop] theorem continuous_vertexCoordinate (v : Fin n ⊕ Fin m) :
    Continuous (fun c : Configuration n m => c.vertexPoint v) :=
  (continuous_apply v).comp continuous_vertexCoordinates

/-- Original vertices, followed by one lower-half-plane conjugate of every interior vertex. -/
abbrev DoubledLabel (n m : ℕ) := (Fin n ⊕ Fin m) ⊕ Fin n

def doubledPoint (c : Configuration n m) : DoubledLabel n m → ℂ
  | Sum.inl v => c.vertexPoint v
  | Sum.inr i => conj (c.interior i : ℂ)

@[fun_prop] theorem continuous_doubledCoordinate (v : DoubledLabel n m) :
    Continuous (fun c : Configuration n m => c.doubledPoint v) := by
  cases v with
  | inl v => exact continuous_vertexCoordinate v
  | inr i =>
    exact Complex.continuous_conj.comp (continuous_vertexCoordinate (Sum.inl i))

theorem doubledPoint_injective (c : Configuration n m) : Function.Injective c.doubledPoint := by
  intro u v h
  cases u with
  | inl u =>
    cases v with
    | inl v => exact congrArg Sum.inl (c.vertexPoint_injective h)
    | inr j =>
      have hi := congrArg Complex.im h
      simp only [doubledPoint, Complex.conj_im, UpperHalfPlane.coe_im] at hi
      have hu := c.vertexPoint_im_nonneg u
      have hj := (c.interior j).im_pos
      linarith
  | inr i =>
    cases v with
    | inl v =>
      have hi := congrArg Complex.im h
      simp only [doubledPoint, Complex.conj_im, UpperHalfPlane.coe_im] at hi
      have hv := c.vertexPoint_im_nonneg v
      have hj := (c.interior i).im_pos
      linarith
    | inr j =>
      apply congrArg Sum.inr
      apply c.interior_injective
      apply UpperHalfPlane.ext
      exact (starRingEnd ℂ).injective h

abbrev DoubledPair (n m : ℕ) :=
  {p : DoubledLabel n m × DoubledLabel n m // p.1 ≠ p.2}

def pairDifference (c : Configuration n m) (p : DoubledPair n m) : ℂ :=
  c.doubledPoint p.val.2 - c.doubledPoint p.val.1

theorem pairDifference_ne_zero (c : Configuration n m) (p : DoubledPair n m) :
    c.pairDifference p ≠ 0 :=
  sub_ne_zero.mpr (fun h => p.property (c.doubledPoint_injective h).symm)

@[fun_prop] theorem continuous_pairDifference (p : DoubledPair n m) :
    Continuous (fun c : Configuration n m => c.pairDifference p) :=
  (continuous_doubledCoordinate p.val.2).sub (continuous_doubledCoordinate p.val.1)

/-- A triple with two targets distinct from the common source; the targets may coincide. -/
abbrev DoubledTriple (n m : ℕ) :=
  {t : DoubledLabel n m × DoubledLabel n m × DoubledLabel n m //
    t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2}

def tripleDistanceRatio (c : Configuration n m) (t : DoubledTriple n m) : Set.Icc (0 : ℝ) 1 :=
  let a := ‖c.pairDifference ⟨(t.val.1, t.val.2.1), t.property.1⟩‖
  let b := ‖c.pairDifference ⟨(t.val.1, t.val.2.2), t.property.2⟩‖
  ⟨a / (a + b), div_nonneg (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _)),
    (div_le_one (add_pos (norm_pos_iff.mpr (c.pairDifference_ne_zero _))
      (norm_pos_iff.mpr (c.pairDifference_ne_zero _)))).mpr (le_add_of_nonneg_right (norm_nonneg _))⟩

@[fun_prop] theorem continuous_tripleDistanceRatio (t : DoubledTriple n m) :
    Continuous (fun c : Configuration n m => c.tripleDistanceRatio t) := by
  apply Continuous.subtype_mk
  apply Continuous.div
  · exact (continuous_pairDifference _).norm
  · exact (continuous_pairDifference _).norm.add (continuous_pairDifference _).norm
  · intro c
    exact ne_of_gt (add_pos (norm_pos_iff.mpr (c.pairDifference_ne_zero _))
      (norm_pos_iff.mpr (c.pairDifference_ne_zero _)))

end Configuration

end EnvelopingIsomorphism.Deformation.Kontsevich
