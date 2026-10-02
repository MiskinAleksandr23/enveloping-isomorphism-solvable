import EnvelopingIsomorphism.Deformation.Kontsevich.ForestEdgeForms
import EnvelopingIsomorphism.Deformation.Kontsevich.ForestMarkedFrameReflection
import EnvelopingIsomorphism.Deformation.Kontsevich.ForestMarkedFrameInverse
import EnvelopingIsomorphism.Deformation.Kontsevich.ForestPositiveScaleAdmissibility

/-! Genuine harmonic graph-edge forms on the real reflected forest parameter
submodule. Numerator and conjugate denominator factor through the actual tree;
the resulting unit form is smooth and closed at every regular corner. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Kontsevich.ForestGraphForms

open Configuration ComplexConjugate ForestInsertionDifference AncestorScaleRatios
open ForestDirectionRatioCoordinates Filter
open scoped Classical Topology

variable {T : RootedTree} [Fintype T] {n m : ℕ} (D : ForestPositiveScale.ShapeData T n m)

/-- All derivatives below live on this actual real reflected submodule. -/
abbrev ParameterSpace := ForestMarkedFrameReflection.parameterSubmodule T D.reflection

def parameterMap : ParameterSpace D →L[ℝ] ForestDirectionRatioCoordinates.Parameters T :=
  (ForestMarkedFrameReflection.parameterSubmodule T D.reflection).subtypeL

def positionMap (j : DoubledLabel n m) (x : ParameterSpace D) : ℂ :=
  position T x.val.1 x.val.2 (D.leaf j)

theorem contDiff_positionMap (j : DoubledLabel n m) : ContDiff ℝ ⊤ (positionMap D j) :=
  (contDiff_position T (D.leaf j)).comp (parameterMap D).contDiff

theorem positionMap_reflection (j : DoubledLabel n m) (x : ParameterSpace D) :
    positionMap D (doubledReflection j) x = conj (positionMap D j x) := by
  unfold positionMap
  rw [← D.leaf_reflect]
  exact ReflectedForestInsertion.position_reflect T D.reflection x.val.1 x.property.1 x.val.2 x.property.2 (D.leaf j)

/-- Reflection is an identity of maps on the entire parameter vector space,
so every tangent direction also satisfies the conjugate derivative identity. -/
theorem fderiv_positionMap_reflection (j : DoubledLabel n m) (x : ParameterSpace D) :
    fderiv ℝ (positionMap D (doubledReflection j)) x =
      (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ (positionMap D j) x) := by
  have h := (Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp x
    ((contDiff_positionMap D j).differentiable (by simp)).differentiableAt.hasFDerivAt
  have he : (fun y : ParameterSpace D => (Complex.conjCLE : ℂ →L[ℝ] ℂ) (positionMap D j y)) =
      positionMap D (doubledReflection j) := funext (fun y => (positionMap_reflection D j y).symm)
  simp only [Function.comp_def] at h
  rw [he] at h
  exact h.fderiv

def unit (p : DoubledPair n m) (x : ParameterSpace D) : ℂ := pairUnit T D.leaf x.val p

def radialScale (p : DoubledPair n m) (x : ParameterSpace D) : ℝ := scale x.val.1 (pairNode T D.leaf p)

theorem contDiff_unit (p : DoubledPair n m) : ContDiff ℝ ⊤ (unit D p) :=
  (contDiff_pairUnit T D.leaf p).comp (parameterMap D).contDiff

theorem contDiff_radialScale (p : DoubledPair n m) : ContDiff ℝ ⊤ (radialScale D p) :=
  (contDiff_scale (pairNode T D.leaf p)).comp (parameterMap D).contDiff.fst

/-- Literal tree insertion produces the monomial-times-unit factorization
globally on the reflected submodule, including zero radial factors. -/
theorem pair_factorization (p : DoubledPair n m) (x : ParameterSpace D) :
    positionMap D p.val.2 x - positionMap D p.val.1 x = (radialScale D p x : ℂ) * unit D p x := by
  simpa only [positionMap, radialScale, unit, Complex.real_smul,
    ForestDirectionRatioCoordinates.pairDifference] using pairDifference_factor T D.leaf x.val p

def Regular (x : ParameterSpace D) : Prop := RegularUnits T D.leaf x.val

theorem isOpen_regular : IsOpen {x : ParameterSpace D | Regular D x} :=
  (isOpen_regularUnits T D.leaf).preimage (parameterMap D).continuous

theorem radialScale_pos (p : DoubledPair n m) (x : ParameterSpace D)
    (hx : ForestMarkedFrameInverse.PositiveInternal T x.val.1) : 0 < radialScale D p x :=
  ForestMarkedFrameInverse.scale_pos_internal T x.val.1 hx _
    (ForestLeafRadii.pairNode_nonleaf T D.leaf D.leaf_injective D.leaf_max p)

def edgeMap (j : Fin n) (v : Fin n ⊕ Fin m) (x : ParameterSpace D) : ℂ × ℂ :=
  (positionMap D (Sum.inl (Sum.inl j)) x, positionMap D (Sum.inl v) x)

theorem contDiff_edgeMap (j : Fin n) (v : Fin n ⊕ Fin m) : ContDiff ℝ ⊤ (edgeMap D j v) :=
  (contDiff_positionMap D _).prodMk (contDiff_positionMap D _)

def numeratorUnit (j : Fin n) (v : Fin n ⊕ Fin m) (hv : v ≠ Sum.inl j) : ParameterSpace D → ℂ :=
  unit D (harmonicNumeratorPair j v hv)

def denominatorUnit (j : Fin n) (v : Fin n ⊕ Fin m) : ParameterSpace D → ℂ :=
  unit D (harmonicDenominatorPair j v)

def numeratorScale (j : Fin n) (v : Fin n ⊕ Fin m) (hv : v ≠ Sum.inl j) : ParameterSpace D → ℝ :=
  radialScale D (harmonicNumeratorPair j v hv)

def denominatorScale (j : Fin n) (v : Fin n ⊕ Fin m) : ParameterSpace D → ℝ :=
  radialScale D (harmonicDenominatorPair j v)

theorem numerator_factorization (j : Fin n) (v : Fin n ⊕ Fin m) (hv : v ≠ Sum.inl j) :
    (fun x : ParameterSpace D => (edgeMap D j v x).2 - (edgeMap D j v x).1) =
      fun x => (numeratorScale D j v hv x : ℂ) * numeratorUnit D j v hv x :=
  funext (pair_factorization D (harmonicNumeratorPair j v hv))

/-- The actual conjugate denominator is identically the mirror-leaf difference
on the real reflected submodule. Its derivative is therefore also correct. -/
theorem denominator_factorization (j : Fin n) (v : Fin n ⊕ Fin m) :
    (fun x : ParameterSpace D => (edgeMap D j v x).2 - conj (edgeMap D j v x).1) =
      fun x => (denominatorScale D j v x : ℂ) * denominatorUnit D j v x := by
  funext x
  have hr := positionMap_reflection D (Sum.inl (Sum.inl j)) x
  change positionMap D (Sum.inr j) x = conj (positionMap D (Sum.inl (Sum.inl j)) x) at hr
  change positionMap D (Sum.inl v) x - conj (positionMap D (Sum.inl (Sum.inl j)) x) = _
  rw [← hr]
  exact pair_factorization D (harmonicDenominatorPair j v) x

def edgeForm (j : Fin n) (v : Fin n ⊕ Fin m) (hv : v ≠ Sum.inl j) (x : ParameterSpace D) :
    ParameterSpace D [⋀^Fin 1]→L[ℝ] ℝ :=
  forestUnitEdgeForm (numeratorUnit D j v hv) (denominatorUnit D j v) x

theorem contDiffAt_edgeForm (j : Fin n) (v : Fin n ⊕ Fin m) (hv : v ≠ Sum.inl j)
    (x : ParameterSpace D) (hx : Regular D x) : ContDiffAt ℝ ⊤ (edgeForm D j v hv) x :=
  contDiffAt_forestUnitEdgeForm _ _ x (contDiff_unit D _).contDiffAt (contDiff_unit D _).contDiffAt
    (hx (harmonicNumeratorPair j v hv)) (hx (harmonicDenominatorPair j v))

theorem contDiffOn_edgeForm (j : Fin n) (v : Fin n ⊕ Fin m) (hv : v ≠ Sum.inl j) :
    ContDiffOn ℝ ⊤ (edgeForm D j v hv) {x | Regular D x} :=
  fun x hx => (contDiffAt_edgeForm D j v hv x hx).contDiffWithinAt

theorem extDeriv_edgeForm (j : Fin n) (v : Fin n ⊕ Fin m) (hv : v ≠ Sum.inl j)
    (x : ParameterSpace D) (hx : Regular D x) : extDeriv (edgeForm D j v hv) x = 0 :=
  extDeriv_forestUnitEdgeForm _ _ x (contDiff_unit D _).contDiffAt (contDiff_unit D _).contDiffAt
    (hx (harmonicNumeratorPair j v hv)) (hx (harmonicDenominatorPair j v))

/-- The extension equals the ACTUAL harmonic pair pullback when internal
radii are positive. Both factorizations are proved from tree insertion;
the two monomial scales may vanish independently on boundary corners. -/
theorem harmonic_pullback_eq_edgeForm (j : Fin n) (v : Fin n ⊕ Fin m) (hv : v ≠ Sum.inl j)
    (x : ParameterSpace D) (hx : Regular D x)
    (hpos : ForestMarkedFrameInverse.PositiveInternal T x.val.1) :
    (harmonicAngleForm (edgeMap D j v x)).compContinuousLinearMap (fderiv ℝ (edgeMap D j v) x) =
      edgeForm D j v hv x := by
  apply harmonicAngleForm_factored_pullback (edgeMap D j v)
    (numeratorScale D j v hv) (denominatorScale D j v) (numeratorUnit D j v hv) (denominatorUnit D j v) x
  · exact ((contDiff_edgeMap D j v).differentiable (by simp)).differentiableAt
  · exact ((contDiff_radialScale D _).differentiable (by simp)).differentiableAt
  · exact ((contDiff_radialScale D _).differentiable (by simp)).differentiableAt
  · exact ((contDiff_unit D _).differentiable (by simp)).differentiableAt
  · exact ((contDiff_unit D _).differentiable (by simp)).differentiableAt
  · exact radialScale_pos D _ x hpos
  · exact radialScale_pos D _ x hpos
  · exact hx (harmonicNumeratorPair j v hv)
  · exact hx (harmonicDenominatorPair j v)
  · exact Filter.Eventually.of_forall (congrFun (numerator_factorization D j v hv))
  · exact Filter.Eventually.of_forall (congrFun (denominator_factorization D j v))

end EnvelopingIsomorphism.Deformation.Kontsevich.ForestGraphForms
