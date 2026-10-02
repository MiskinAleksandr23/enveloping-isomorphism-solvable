import EnvelopingIsomorphism.Deformation.Kontsevich.LogMonomialBoundaryPrimitive

/-! Local L1 estimates for the actual logarithmic primitive and its exterior derivative.
The primitive multiplier is bounded from lower and upper unit norms. Its tail
determinant has only simple radial poles by the proved monomial matrix identity.
The exterior derivative is identified using genuine C2 pullback exactness.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.LogMonomial

open MeasureTheory Set
open scoped BigOperators Topology

/-- Lower and upper norm bounds control the actual unit logarithm. -/
theorem abs_log_norm_le_of_unitBounds {u : ℂ} {c M : ℝ} (hc : 0 < c)
    (hlo : c ≤ ‖u‖) (hhi : ‖u‖ ≤ M) :
    |Real.log ‖u‖| ≤ max |Real.log c| |Real.log M| := by
  apply abs_le.mpr
  constructor
  · exact (neg_le_neg (le_max_left _ _)).trans
      ((neg_abs_le (Real.log c)).trans (Real.log_le_log hc hlo))
  · exact (Real.log_le_log (hc.trans_le hlo) hhi).trans
      ((le_abs_self _).trans (le_max_right _ _))

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

omit [Fintype I] [DecidableEq I] [DecidableEq J] in
/-- Finite smoothness of an actual integer monomial on the nonzero coordinate locus. -/
theorem contDiffAt_coordinateMonomial (a : I → J → ℤ) (u : I → (J → ℂ) → ℂ)
    (i : I) (x : J → ℂ) {k : WithTop ℕ∞}
    (hu : ContDiffAt ℝ k (u i) x) (hx : ∀ ν, x ν ≠ 0) :
    ContDiffAt ℝ k (coordinateMonomial a u i) x := by
  classical
  have hcoord (ν : J) : ContDiffAt ℝ k (fun y : J → ℂ => y ν) x :=
    (contDiff_apply ℝ ℂ ν).contDiffAt
  have hpow (ν : J) : ContDiffAt ℝ k (fun y : J → ℂ => y ν ^ a i ν) x := by
    cases a i ν with
    | ofNat m =>
      convert! (hcoord ν).pow m using 1
    | negSucc m =>
      convert! ((hcoord ν).pow (m + 1)).inv (pow_ne_zero _ (hx ν)) using 1
  have hp (s : Finset J) : ContDiffAt ℝ k (fun y : J → ℂ => ∏ ν ∈ s, y ν ^ a i ν) x := by
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.prod_empty] using (contDiffAt_const (c := (1 : ℂ)))
    | @insert ν s hν ih =>
      simp only [Finset.prod_insert hν]
      exact (hpow ν).mul ih
  exact hu.mul (hp Finset.univ)

/-- Actual determinant continuity follows from the proved matrix identity, locally. -/
theorem continuousOn_actualRadialDeterminant_of_localC1
    (a : I → J → ℤ) (u : I → (J → ℂ) → ℂ) (v : I → J → ℂ) (ε : J → ℝ)
    (U : Set (J → ℂ)) (hU : IsOpen U) (hsub : NormalCrossing.puncturedPolydisc ε ⊆ U)
    (hu : ∀ i, ContDiffOn ℝ 1 (u i) U)
    (hunit : ∀ x ∈ NormalCrossing.puncturedPolydisc ε, ∀ i, u i x ≠ 0) :
    ContinuousOn (fun x => Matrix.det (actualRadialMatrix a u v x))
      (NormalCrossing.puncturedPolydisc ε) := by
  apply (continuousOn_modelDeterminant_of_localC1 a u v ε U hU hsub hu hunit).congr
  intro x hx
  change Matrix.det (actualRadialMatrix a u v x) = _
  rw [actualRadialMatrix_eq a u v
    (fun i => ((hu i).contDiffAt (hU.mem_nhds (hsub hx))).differentiableAt (by norm_num))
    (hunit x hx) (fun ν => norm_pos_iff.mp ((hx ν (mem_univ ν)).1))]
  rfl

variable {n : ℕ}

/-- The completely explicit bulk primitive majorant constant. -/
def primitiveIntegrabilityBound (a : Fin (n + 1) → J → ℤ) (D c M : ℝ) : ℝ :=
  logarithmBound (a 0) (max |Real.log c| |Real.log M|) *
    uniformDeterminantBound (fun i : Fin n => a i.succ) D c

/-- The actual primitive coefficient is continuous on the actual punctured polydisc. -/
theorem continuousOn_primitiveCoefficient_of_localC1
    (a : Fin (n + 1) → J → ℤ) (u : Fin (n + 1) → (J → ℂ) → ℂ)
    (v : Fin n → J → ℂ) (ε : J → ℝ)
    (U : Set (J → ℂ)) (hU : IsOpen U) (hsub : NormalCrossing.puncturedPolydisc ε ⊆ U)
    (hu : ∀ i, ContDiffOn ℝ 1 (u i) U)
    (hunit : ∀ x ∈ NormalCrossing.puncturedPolydisc ε, ∀ i, u i x ≠ 0) :
    ContinuousOn (fun x => LogRadialPrimitive.primitive (coordinateMonomial a u) x v)
      (NormalCrossing.puncturedPolydisc ε) := by
  have hux (x : J → ℂ) (hx : x ∈ NormalCrossing.puncturedPolydisc ε) (i : Fin (n + 1)) :
      ContDiffAt ℝ 1 (u i) x := (hu i).contDiffAt (hU.mem_nhds (hsub hx))
  have hx0 (x : J → ℂ) (hx : x ∈ NormalCrossing.puncturedPolydisc ε) (ν : J) : x ν ≠ 0 :=
    norm_pos_iff.mp ((hx ν (mem_univ ν)).1)
  have hm : ContinuousOn (coordinateMonomial a u 0) (NormalCrossing.puncturedPolydisc ε) := by
    intro x hx
    exact (contDiffAt_coordinateMonomial a u 0 x (hux x hx 0) (hx0 x hx)).continuousAt.continuousWithinAt
  have hlog := hm.norm.log (fun x hx => norm_ne_zero_iff.mpr (value_ne_zero (a 0) (hunit x hx 0) (hx0 x hx)))
  have hd := continuousOn_actualRadialDeterminant_of_localC1
    (fun i : Fin n => a i.succ) (fun i => u i.succ) v ε U hU hsub
    (fun i => hu i.succ) (fun x hx i => hunit x hx i.succ)
  apply (hlog.mul hd).congr
  intro x hx
  exact primitive_eq_log_mul_actualDeterminant a u v x
    (fun i => (hux x hx i).differentiableAt (by norm_num)) (hunit x hx) (hx0 x hx)

/-- Repeated poles cancel before bounding the actual primitive; its logarithmic
multiplier costs only one integrable logarithmic factor in each normal coordinate. -/
theorem norm_primitiveCoefficient_le_majorant
    (a : Fin (n + 1) → J → ℤ) (u : Fin (n + 1) → (J → ℂ) → ℂ)
    (v : Fin n → J → ℂ) (x : J → ℂ)
    (hu : ∀ i, DifferentiableAt ℝ (u i) x) (hx : ∀ ν, x ν ≠ 0)
    (D c M : ℝ) (hc : 0 < c)
    (hD : ∀ i : Fin n, ‖fderiv ℝ (u i.succ) x‖ ≤ D)
    (hunit : ∀ i, c ≤ ‖u i x‖) (hupper : ‖u 0 x‖ ≤ M) (hv : ∀ j, ‖v j‖ ≤ 1) :
    ‖LogRadialPrimitive.primitive (coordinateMonomial a u) x v‖ ≤
      primitiveIntegrabilityBound a D c M * NormalCrossing.majorant (fun _ : J => 1) x := by
  have hu0 (i : Fin (n + 1)) : u i x ≠ 0 := norm_pos_iff.mp (hc.trans_le (hunit i))
  have hlog := abs_log_norm_value_le (a 0) (hu0 0) hx _
    (abs_log_norm_le_of_unitBounds hc (hunit 0) hupper)
  have hd := (abs_actualRadialMatrix_det_le (fun i : Fin n => a i.succ) (fun i => u i.succ)
    v (fun i => hu i.succ) (fun i => hu0 i.succ) hx).trans
    (mul_le_mul_of_nonneg_right
      (coefficientBound_le_unitBounds (fun i : Fin n => a i.succ) (fun i => u i.succ)
        v x D c hc hD (fun i => hunit i.succ) hv)
      (Finset.prod_nonneg fun _ _ => by positivity))
  have hK := logarithmBound_nonneg (a 0) (L := max |Real.log c| |Real.log M|)
    (le_max_of_le_left (abs_nonneg (Real.log c)))
  rw [primitive_eq_log_mul_actualDeterminant a u v x hu hu0 hx, norm_mul,
    Real.norm_eq_abs, Real.norm_eq_abs]
  apply (mul_le_mul hlog hd (abs_nonneg _) (by positivity)).trans_eq
  simp only [primitiveIntegrabilityBound, NormalCrossing.majorant_eq_prod_mul, pow_one]
  ring

/-- Bulk L1 of the actual primitive from local C1 units and numerical unit bounds.
No measurability, integrability or bound for the whole primitive is an input. -/
theorem integrableOn_primitiveCoefficient_of_localC1
    (a : Fin (n + 1) → J → ℤ) (u : Fin (n + 1) → (J → ℂ) → ℂ)
    (v : Fin n → J → ℂ) (ε : J → ℝ)
    (U : Set (J → ℂ)) (hU : IsOpen U) (hsub : NormalCrossing.puncturedPolydisc ε ⊆ U)
    (hu : ∀ i, ContDiffOn ℝ 1 (u i) U) (D c M : ℝ) (hc : 0 < c)
    (hD : ∀ x ∈ NormalCrossing.puncturedPolydisc ε, ∀ i : Fin n,
      ‖fderiv ℝ (u i.succ) x‖ ≤ D)
    (hunit : ∀ x ∈ NormalCrossing.puncturedPolydisc ε, ∀ i, c ≤ ‖u i x‖)
    (hupper : ∀ x ∈ NormalCrossing.puncturedPolydisc ε, ‖u 0 x‖ ≤ M)
    (hv : ∀ j, ‖v j‖ ≤ 1) :
    IntegrableOn (fun x => LogRadialPrimitive.primitive (coordinateMonomial a u) x v)
      (NormalCrossing.puncturedPolydisc ε) := by
  have hcont := continuousOn_primitiveCoefficient_of_localC1 a u v ε U hU hsub hu
    (fun x hx i => norm_pos_iff.mp (hc.trans_le (hunit x hx i)))
  apply NormalCrossing.integrableOn_of_norm_le_majorant_on (fun _ : J => 1) ε _
    (primitiveIntegrabilityBound a D c M)
    (hcont.aestronglyMeasurable (NormalCrossing.measurableSet_puncturedPolydisc ε))
  intro x hx
  exact norm_primitiveCoefficient_le_majorant a u v x
    (fun i => ((hu i).contDiffAt (hU.mem_nhds (hsub hx))).differentiableAt (by norm_num))
    (fun ν => norm_pos_iff.mp ((hx ν (mem_univ ν)).1)) D c M hc
    (hD x hx) (hunit x hx) (hupper x hx) hv

end EnvelopingIsomorphism.Deformation.Kontsevich.LogMonomial

namespace EnvelopingIsomorphism.Deformation.Kontsevich.LogRadialPrimitive

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

/-- Genuine finite C2 regularity suffices for the actual primitive's exactness.
This is the same pullback identity without an analytic-order hypothesis. -/
theorem extDeriv_primitive_of_C2 (f : Fin (n + 1) → E → ℂ) {x : E}
    (hf : ∀ i, ContDiffAt ℝ 2 (f i) x) (hne : ∀ i, f i x ≠ 0) :
    extDeriv (primitive f) x = radialForm f x := by
  have hlog : ContDiffAt ℝ 2 (logarithms f) x := by
    apply contDiffAt_pi.mpr
    intro i
    exact ((hf i).norm ℂ (hne i)).log (norm_ne_zero_iff.mpr (hne i))
  unfold primitive
  rw [extDeriv_pullback
    ((contDiff_coordinatePrimitive n).differentiable (by simp)).differentiableAt hlog (by norm_num),
    extDeriv_coordinatePrimitive,
    (hasFDerivAt_logarithms f (fun i => (hf i).differentiableAt (by norm_num)) hne).fderiv]
  rfl

end EnvelopingIsomorphism.Deformation.Kontsevich.LogRadialPrimitive

namespace EnvelopingIsomorphism.Deformation.Kontsevich.LogMonomial

open MeasureTheory Set
open scoped BigOperators Topology

variable {J : Type*} [Fintype J] [DecidableEq J] {n : ℕ}

omit [DecidableEq J] in
/-- The actual exterior derivative coefficient is the full actual monomial determinant. -/
theorem extDeriv_primitive_eq_actualDeterminant_of_C2
    (a : Fin (n + 1) → J → ℤ) (u : Fin (n + 1) → (J → ℂ) → ℂ)
    (v : Fin (n + 1) → J → ℂ) (x : J → ℂ)
    (hu : ∀ i, ContDiffAt ℝ 2 (u i) x) (hu0 : ∀ i, u i x ≠ 0) (hx : ∀ ν, x ν ≠ 0) :
    extDeriv (LogRadialPrimitive.primitive (coordinateMonomial a u)) x v =
      Matrix.det (actualRadialMatrix a u v x) := by
  rw [LogRadialPrimitive.extDeriv_primitive_of_C2 _
    (fun i => contDiffAt_coordinateMonomial a u i x (hu i) hx)
    (fun i => value_ne_zero (a i) (hu0 i) hx), LogRadialPrimitive.radialForm_apply]
  change Matrix.det (Matrix.transpose (actualRadialMatrix a u v x)) = _
  exact Matrix.det_transpose _

/-- Bulk L1 of the actual exterior derivative, from local C2 units and their
first-derivative/lower-norm bounds. No upper norm bound is needed for dβ. -/
theorem integrableOn_extDeriv_primitiveCoefficient_of_localC2
    (a : Fin (n + 1) → J → ℤ) (u : Fin (n + 1) → (J → ℂ) → ℂ)
    (v : Fin (n + 1) → J → ℂ) (ε : J → ℝ)
    (U : Set (J → ℂ)) (hU : IsOpen U) (hsub : NormalCrossing.puncturedPolydisc ε ⊆ U)
    (hu : ∀ i, ContDiffOn ℝ 2 (u i) U) (D c : ℝ) (hc : 0 < c)
    (hD : ∀ x ∈ NormalCrossing.puncturedPolydisc ε, ∀ i, ‖fderiv ℝ (u i) x‖ ≤ D)
    (hunit : ∀ x ∈ NormalCrossing.puncturedPolydisc ε, ∀ i, c ≤ ‖u i x‖)
    (hv : ∀ j, ‖v j‖ ≤ 1) :
    IntegrableOn
      (fun x => extDeriv (LogRadialPrimitive.primitive (coordinateMonomial a u)) x v)
      (NormalCrossing.puncturedPolydisc ε) := by
  have hi := integrableOn_weightedActualDeterminant_of_localC1 a u v (fun _ => 0) ε U hU hsub
    (fun i => (hu i).of_le (by norm_num)) D c hc hD hunit hv
  apply hi.congr_fun _ (NormalCrossing.measurableSet_puncturedPolydisc ε)
  intro x hx
  simp only [weightedActualDeterminant, NormalCrossingDeterminantIntegrability.logWeight,
    pow_zero, Finset.prod_const_one, mul_one]
  exact (extDeriv_primitive_eq_actualDeterminant_of_C2 a u v x
    (fun i => (hu i).contDiffAt (hU.mem_nhds (hsub hx)))
    (fun i => norm_pos_iff.mp (hc.trans_le (hunit x hx i)))
    (fun ν => norm_pos_iff.mp ((hx ν (mem_univ ν)).1))).symm

/-- Both actual coefficients β and dβ are L1 before any distributional or global
Stokes argument. The two fixed tangent tuples can be chosen independently. -/
theorem integrableOn_primitive_and_extDeriv_of_localC2
    (a : Fin (n + 1) → J → ℤ) (u : Fin (n + 1) → (J → ℂ) → ℂ)
    (v : Fin n → J → ℂ) (w : Fin (n + 1) → J → ℂ) (ε : J → ℝ)
    (U : Set (J → ℂ)) (hU : IsOpen U) (hsub : NormalCrossing.puncturedPolydisc ε ⊆ U)
    (hu : ∀ i, ContDiffOn ℝ 2 (u i) U) (D c M : ℝ) (hc : 0 < c)
    (hD : ∀ x ∈ NormalCrossing.puncturedPolydisc ε, ∀ i, ‖fderiv ℝ (u i) x‖ ≤ D)
    (hunit : ∀ x ∈ NormalCrossing.puncturedPolydisc ε, ∀ i, c ≤ ‖u i x‖)
    (hupper : ∀ x ∈ NormalCrossing.puncturedPolydisc ε, ‖u 0 x‖ ≤ M)
    (hv : ∀ j, ‖v j‖ ≤ 1) (hw : ∀ j, ‖w j‖ ≤ 1) :
    IntegrableOn (fun x => LogRadialPrimitive.primitive (coordinateMonomial a u) x v)
      (NormalCrossing.puncturedPolydisc ε) ∧
    IntegrableOn (fun x => extDeriv (LogRadialPrimitive.primitive (coordinateMonomial a u)) x w)
      (NormalCrossing.puncturedPolydisc ε) := by
  constructor
  · exact integrableOn_primitiveCoefficient_of_localC1 a u v ε U hU hsub
      (fun i => (hu i).of_le (by norm_num)) D c M hc
      (fun x hx i => hD x hx i.succ) hunit hupper hv
  · exact integrableOn_extDeriv_primitiveCoefficient_of_localC2 a u w ε U hU hsub
      hu D c hc hD hunit hw

end EnvelopingIsomorphism.Deformation.Kontsevich.LogMonomial
