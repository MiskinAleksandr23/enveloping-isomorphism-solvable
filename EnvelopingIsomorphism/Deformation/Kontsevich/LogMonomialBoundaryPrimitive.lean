import EnvelopingIsomorphism.Deformation.Kontsevich.LogMonomialBoundaryMatrix
import EnvelopingIsomorphism.Deformation.Kontsevich.LogMonomialIntegrability
import EnvelopingIsomorphism.Deformation.Kontsevich.LogRadialPrimitive
import EnvelopingIsomorphism.Deformation.Kontsevich.NormalCrossingBoundaryFlux

/-! The actual logarithmic primitive on a literal normal-coordinate circle face.
The logarithmic multiplier is estimated from its integer exponents and unit.
The remaining coefficient bound and measurable chart data are explicit local inputs.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.LogMonomial

open MeasureTheory Set Filter
open scoped BigOperators Topology

variable {J : Type*} [Fintype J]

/-- The constant controlling the actual monomial logarithm. -/
def logarithmBound (a : J → ℤ) (L : ℝ) : ℝ := L + ∑ ν, |(a ν : ℝ)|

theorem logarithmBound_nonneg (a : J → ℤ) {L : ℝ} (hL : 0 ≤ L) :
    0 ≤ logarithmBound a L := add_nonneg hL (Finset.sum_nonneg fun _ _ => abs_nonneg _)

/-- This estimate is derived from the exact monomial log formula, including negative exponents. -/
theorem abs_log_norm_value_le (a : J → ℤ) {u : ℂ} {x : J → ℂ}
    (hu : u ≠ 0) (hx : ∀ ν, x ν ≠ 0) (L : ℝ) (hL : |Real.log ‖u‖| ≤ L) :
    |Real.log ‖value a u x‖| ≤ logarithmBound a L * ∏ ν, (1 + |Real.log ‖x ν‖|) := by
  let P := ∏ ν, (1 + |Real.log ‖x ν‖|)
  have hP : 1 ≤ P := Finset.one_le_prod fun ν _ => le_add_of_nonneg_right (abs_nonneg _)
  have hν (ν : J) : |Real.log ‖x ν‖| ≤ P := by
    have h := Finset.le_prod_max_one (Finset.mem_univ ν) (fun ν => 1 + |Real.log ‖x ν‖|)
    have he (ν : J) : max (1 + |Real.log ‖x ν‖|) 1 = 1 + |Real.log ‖x ν‖| :=
      max_eq_left (le_add_of_nonneg_right (abs_nonneg _))
    simp only [he] at h
    exact (le_add_of_nonneg_left zero_le_one).trans h
  rw [log_norm_value a hu hx]
  calc
    |Real.log ‖u‖ + ∑ ν, (a ν : ℝ) * Real.log ‖x ν‖| ≤
        |Real.log ‖u‖| + ∑ ν, |(a ν : ℝ)| * |Real.log ‖x ν‖| := by
      simpa only [abs_mul] using (abs_add_le (Real.log ‖u‖)
        (∑ ν, (a ν : ℝ) * Real.log ‖x ν‖)).trans
        (add_le_add (le_refl |Real.log ‖u‖|)
          (Finset.abs_sum_le_sum_abs (fun ν => (a ν : ℝ) * Real.log ‖x ν‖) Finset.univ))
    _ ≤ L * P + ∑ ν, |(a ν : ℝ)| * P := by
      gcongr
      · exact hL.trans (le_mul_of_one_le_right ((abs_nonneg _).trans hL) hP)
      · exact hν _
    _ = _ := by rw [← Finset.sum_mul, ← add_mul]; rfl

variable [DecidableEq J] {n : ℕ}

omit [DecidableEq J] in
/-- Evaluation of the previously constructed actual primitive, with the row convention
of the actual monomial matrix. The transpose contributes no sign. -/
theorem primitive_eq_log_mul_actualDeterminant
    (a : Fin (n + 1) → J → ℤ) (u : Fin (n + 1) → (J → ℂ) → ℂ)
    (v : Fin n → J → ℂ) (x : J → ℂ)
    (hu : ∀ i, DifferentiableAt ℝ (u i) x) (hu0 : ∀ i, u i x ≠ 0) (hx : ∀ ν, x ν ≠ 0) :
    LogRadialPrimitive.primitive (coordinateMonomial a u) x v =
      Real.log ‖value (a 0) (u 0 x) x‖ *
        Matrix.det (actualRadialMatrix (fun i : Fin n => a i.succ) (fun i => u i.succ) v x) := by
  have hf (i : Fin (n + 1)) : DifferentiableAt ℝ (coordinateMonomial a u i) x :=
    differentiableAt_function (a i) (u i) (fun ν y => y ν) (hu i)
      (fun ν => (ContinuousLinearMap.proj ν : (J → ℂ) →L[ℝ] ℂ).differentiableAt) hx
  rw [LogRadialPrimitive.primitive_apply _ hf (fun i => value_ne_zero (a i) (hu0 i) hx)]
  change _ * Matrix.det (Matrix.transpose
    (actualRadialMatrix (fun i : Fin n => a i.succ) (fun i => u i.succ) v x)) = _
  rw [Matrix.det_transpose]
  rfl

/-- The literal circle-face parametrization: `none` is the distinguished normal coordinate. -/
def circleFacePoint (r : ℝ) (p : ℝ × (J → ℂ)) : Option J → ℂ :=
  fun ν => ν.elim ((r : ℂ) * circleParameter p.1) p.2

omit [Fintype J] [DecidableEq J] in
@[simp] theorem norm_circleFacePoint_none (r : ℝ) (p : ℝ × (J → ℂ)) :
    ‖circleFacePoint r p none‖ = |r| := by
  simp [circleFacePoint, circleParameter_eq]

omit [Fintype J] [DecidableEq J] in
@[simp] theorem circleFacePoint_some (r : ℝ) (p : ℝ × (J → ℂ)) (ν : J) :
    circleFacePoint r p (some ν) = p.2 ν := rfl

omit [Fintype J] in
/-- The angular boundary tangent is the actual derivative of the circle-face parametrization. -/
theorem hasDerivAt_circleFacePoint (r θ : ℝ) (z : J → ℂ) :
    HasDerivAt (fun t => circleFacePoint r (t, z))
      (r • unitAngularTangent none θ) θ := by
  apply hasDerivAt_pi.mpr
  intro ν
  cases ν with
  | none =>
    have h := (hasFDerivAt_circleParameter θ).hasDerivAt.const_mul (r : ℂ)
    simpa [circleFacePoint, unitAngularTangent, Complex.real_smul,
      circleParameterTangent_apply, mul_comm] using h
  | some ν =>
    simpa [circleFacePoint, unitAngularTangent] using (hasDerivAt_const θ (z ν))

omit [Fintype J] [DecidableEq J] in
theorem circleFacePoint_ne_zero (r : ℝ) (hr : 0 < r) (p : ℝ × (J → ℂ))
    (ε : J → ℝ) (hp : p ∈ NormalCrossing.boundaryRegion ε) :
    ∀ ν, circleFacePoint r p ν ≠ 0 := by
  intro ν
  cases ν with
  | none => exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne') (circleParameter_ne_zero _)
  | some ν => exact norm_pos_iff.mp ((hp.2 ν (mem_univ ν)).1)

theorem prod_erase_none_poles (r : ℝ) (p : ℝ × (J → ℂ)) :
    (∏ ν ∈ Finset.univ.erase (none : Option J), max 1 (1 / ‖circleFacePoint r p ν‖)) =
      ∏ ν, max 1 (1 / ‖p.2 ν‖) := by
  let f := fun ν => max 1 (1 / ‖circleFacePoint r p ν‖)
  have h := Finset.mul_prod_erase Finset.univ f (Finset.mem_univ (none : Option J))
  rw [Fintype.prod_option] at h
  exact mul_left_cancel₀ (by dsimp [f]; positivity) h

/-- The concrete coefficient left after removing the boundary radius and distinguished pole. -/
def boundaryCoefficient (a : Fin n → Option J → ℤ)
    (u : Fin n → (Option J → ℂ) → ℂ) (v : Fin n → Option J → ℂ)
    (x : Option J → ℂ) (j₀ : Fin n) (θ : ℝ) : ℝ :=
  RadialPoleDeterminant.coefficientBound
    ((smoothRows u v x).updateCol j₀ (angularUnitColumn u none θ x))
    (unitRadialRows v x) (integerCoefficients a)

theorem norm_unitAngularTangent_le (ν₀ : J) (θ : ℝ) :
    ‖unitAngularTangent ν₀ θ‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro ν
  by_cases hν : ν = ν₀
  · subst ν
    simp [unitAngularTangent, circleParameter_eq]
  · simp [unitAngularTangent, hν]

/-- The regularized coefficient bound follows from true unit derivative bounds;
the angular column uses its unit tangent after the radius was extracted. -/
theorem boundaryCoefficient_le_unitBounds (a : Fin n → Option J → ℤ)
    (u : Fin n → (Option J → ℂ) → ℂ) (v : Fin n → Option J → ℂ)
    (x : Option J → ℂ) (j₀ : Fin n) (θ D c : ℝ) (hc : 0 < c)
    (hD : ∀ i, ‖fderiv ℝ (u i) x‖ ≤ D) (hunit : ∀ i, c ≤ ‖u i x‖)
    (hv : ∀ j, ‖v j‖ ≤ 1) :
    boundaryCoefficient a u v x j₀ θ ≤ uniformDeterminantBound a D c := by
  apply RadialPoleDeterminant.coefficientBound_le_uniform _ _ _
    (max 1 (D / c)) (exponentBound a) (le_max_left _ _) (one_le_exponentBound a)
  · intro i j
    by_cases hj : j = j₀
    · subst j
      simp only [Matrix.updateCol_self]
      exact (smoothRows_bound u (fun _ => unitAngularTangent none θ) x D c hc hD hunit
        (fun _ => norm_unitAngularTangent_le none θ) i j₀).trans (le_max_right _ _)
    · rw [Matrix.updateCol_apply, if_neg hj]
      exact (smoothRows_bound u v x D c hc hD hunit hv i j).trans (le_max_right _ _)
  · intro ν j
    exact (unitRadialRows_bound_one v hv x ν j).trans (le_max_left _ _)
  · exact integerCoefficients_bound a

/-- The actual primitive has an integrable simple-pole/logarithmic majorant on the face.
No representation identity or bound for the whole primitive is assumed. -/
theorem norm_primitive_circleFace_le
    (a : Fin (n + 1) → Option J → ℤ) (u : Fin (n + 1) → (Option J → ℂ) → ℂ)
    (v : Fin n → Option J → ℂ) (j₀ : Fin n) (r : ℝ) (hr : 0 < r)
    (p : ℝ × (J → ℂ)) (ε : J → ℝ) (hp : p ∈ NormalCrossing.boundaryRegion ε)
    (hu : ∀ i, DifferentiableAt ℝ (u i) (circleFacePoint r p))
    (hu0 : ∀ i, u i (circleFacePoint r p) ≠ 0)
    (hv₀ : v j₀ = r • unitAngularTangent none p.1)
    (hvrest : ∀ j, j ≠ j₀ → v j none = 0)
    (C L : ℝ) (_hC : 0 ≤ C)
    (hcoeff : boundaryCoefficient (fun i : Fin n => a i.succ) (fun i => u i.succ) v
      (circleFacePoint r p) j₀ p.1 ≤ C)
    (hL : |Real.log ‖u 0 (circleFacePoint r p)‖| ≤ L) :
    ‖LogRadialPrimitive.primitive (coordinateMonomial a u) (circleFacePoint r p) v‖ ≤
      C * logarithmBound (a 0) L * r * (1 + |Real.log r|) *
        NormalCrossing.boundaryMajorant (fun _ : J => 1) p := by
  have hx := circleFacePoint_ne_zero r hr p ε hp
  have hlog := abs_log_norm_value_le (a 0) (hu0 0) hx L hL
  rw [Fintype.prod_option, norm_circleFacePoint_none, abs_of_pos hr] at hlog
  have hd := abs_actualRadialMatrix_boundary_le (fun i : Fin n => a i.succ) (fun i => u i.succ)
    v (circleFacePoint r p) j₀ none r p.1 hr.le rfl hv₀ hvrest
    (fun i => hu i.succ) (fun i => hu0 i.succ) hx
  rw [prod_erase_none_poles] at hd
  have hd' := hd.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hcoeff hr.le) (Finset.prod_nonneg fun _ _ => by positivity))
  rw [primitive_eq_log_mul_actualDeterminant a u v _ hu hu0 hx, norm_mul,
    Real.norm_eq_abs, Real.norm_eq_abs]
  have hK := logarithmBound_nonneg (a 0) ((abs_nonneg _).trans hL)
  have h := mul_le_mul hlog hd' (abs_nonneg _) (by positivity)
  refine h.trans_eq ?_
  simp only [NormalCrossing.boundaryMajorant, NormalCrossing.majorant_eq_prod_mul, pow_one,
    circleFacePoint_some]
  ring

/-- Evaluation of the actual primitive on a parameter-dependent boundary frame. -/
def circleFacePrimitive (a : Fin (n + 1) → Option J → ℤ)
    (u : Fin (n + 1) → (Option J → ℂ) → ℂ)
    (v : ℝ → (ℝ × (J → ℂ)) → Fin n → Option J → ℂ)
    (r : ℝ) (p : ℝ × (J → ℂ)) : ℝ :=
  LogRadialPrimitive.primitive (coordinateMonomial a u) (circleFacePoint r p) (v r p)

/-- The explicit finite normal-crossing bound for one primitive flux. -/
def primitiveFluxBound (ε : J → ℝ) (C K r : ℝ) : ℝ :=
  (2 * Real.pi) * C * K * r * (1 + |Real.log r|) *
    ∫ z in NormalCrossing.puncturedPolydisc ε, NormalCrossing.majorant (fun _ : J => 1) z

omit [DecidableEq J] in
theorem tendsto_primitiveFluxBound (ε : J → ℝ) (C K : ℝ) :
    Tendsto (primitiveFluxBound ε C K) (𝓝[>] 0) (𝓝 0) := by
  have h := (NormalCrossing.tendsto_fluxBound (fun _ : J => 1) ε 0 (C * K)).add
    (NormalCrossing.tendsto_fluxBound (fun _ : J => 1) ε 1 (C * K))
  convert h using 1
  · funext r
    simp only [primitiveFluxBound, NormalCrossing.fluxBound, pow_zero, pow_one]
    ring
  · simp

/-- Local quantitative bounds on the units and the extracted determinant coefficient
give genuine integrability and a bound for the actual primitive's boundary integral. -/
theorem circleFacePrimitive_flux_spec
    (a : Fin (n + 1) → Option J → ℤ) (u : Fin (n + 1) → (Option J → ℂ) → ℂ)
    (v : ℝ → (ℝ × (J → ℂ)) → Fin n → Option J → ℂ)
    (j₀ : Fin n) (ε : J → ℝ) (C L r : ℝ) (hr : 0 < r) (hC : 0 ≤ C)
    (hF : AEStronglyMeasurable (circleFacePrimitive a u v r)
      (volume.restrict (NormalCrossing.boundaryRegion ε)))
    (hu : ∀ p ∈ NormalCrossing.boundaryRegion ε, ∀ i,
      DifferentiableAt ℝ (u i) (circleFacePoint r p))
    (hu0 : ∀ p ∈ NormalCrossing.boundaryRegion ε, ∀ i, u i (circleFacePoint r p) ≠ 0)
    (hv₀ : ∀ p ∈ NormalCrossing.boundaryRegion ε,
      v r p j₀ = r • unitAngularTangent none p.1)
    (hvrest : ∀ p ∈ NormalCrossing.boundaryRegion ε, ∀ j, j ≠ j₀ → v r p j none = 0)
    (hcoeff : ∀ p ∈ NormalCrossing.boundaryRegion ε,
      boundaryCoefficient (fun i : Fin n => a i.succ) (fun i => u i.succ) (v r p)
        (circleFacePoint r p) j₀ p.1 ≤ C)
    (hL : ∀ p ∈ NormalCrossing.boundaryRegion ε, |Real.log ‖u 0 (circleFacePoint r p)‖| ≤ L) :
    IntegrableOn (circleFacePrimitive a u v r) (NormalCrossing.boundaryRegion ε) ∧
      ‖∫ p in NormalCrossing.boundaryRegion ε, circleFacePrimitive a u v r p‖ ≤
        primitiveFluxBound ε C (logarithmBound (a 0) L) r := by
  have hmajor := (NormalCrossing.integrableOn_boundaryMajorant (fun _ : J => 1) ε).const_mul
    (C * logarithmBound (a 0) L * r * (1 + |Real.log r|))
  have hbound : ∀ᵐ p ∂(volume.restrict (NormalCrossing.boundaryRegion ε)),
      ‖circleFacePrimitive a u v r p‖ ≤ C * logarithmBound (a 0) L * r *
        (1 + |Real.log r|) * NormalCrossing.boundaryMajorant (fun _ : J => 1) p := by
    filter_upwards [ae_restrict_mem (NormalCrossing.measurableSet_boundaryRegion ε)] with p hp
    exact norm_primitive_circleFace_le a u (v r p) j₀ r hr p ε hp
      (hu p hp) (hu0 p hp) (hv₀ p hp) (hvrest p hp) C L hC (hcoeff p hp) (hL p hp)
  refine ⟨hmajor.mono' hF hbound, ?_⟩
  have h := norm_integral_le_of_norm_le hmajor hbound
  rw [integral_const_mul, NormalCrossing.integral_boundaryMajorant] at h
  exact h.trans_eq (by unfold primitiveFluxBound; ring)

/-- A version with no supplied determinant coefficient bound: it is computed from
the finite exponent array, actual derivative norm bounds, and a lower bound for the units. -/
theorem circleFacePrimitive_flux_spec_of_unitBounds
    (a : Fin (n + 1) → Option J → ℤ) (u : Fin (n + 1) → (Option J → ℂ) → ℂ)
    (v : ℝ → (ℝ × (J → ℂ)) → Fin n → Option J → ℂ)
    (j₀ : Fin n) (ε : J → ℝ) (D c L r : ℝ) (hr : 0 < r) (hc : 0 < c)
    (hF : AEStronglyMeasurable (circleFacePrimitive a u v r)
      (volume.restrict (NormalCrossing.boundaryRegion ε)))
    (hu : ∀ p ∈ NormalCrossing.boundaryRegion ε, ∀ i,
      DifferentiableAt ℝ (u i) (circleFacePoint r p))
    (hunit : ∀ p ∈ NormalCrossing.boundaryRegion ε, ∀ i,
      c ≤ ‖u i (circleFacePoint r p)‖)
    (hD : ∀ p ∈ NormalCrossing.boundaryRegion ε, ∀ i : Fin n,
      ‖fderiv ℝ (u i.succ) (circleFacePoint r p)‖ ≤ D)
    (hv : ∀ p ∈ NormalCrossing.boundaryRegion ε, ∀ j, ‖v r p j‖ ≤ 1)
    (hv₀ : ∀ p ∈ NormalCrossing.boundaryRegion ε,
      v r p j₀ = r • unitAngularTangent none p.1)
    (hvrest : ∀ p ∈ NormalCrossing.boundaryRegion ε, ∀ j, j ≠ j₀ → v r p j none = 0)
    (hL : ∀ p ∈ NormalCrossing.boundaryRegion ε, |Real.log ‖u 0 (circleFacePoint r p)‖| ≤ L) :
    IntegrableOn (circleFacePrimitive a u v r) (NormalCrossing.boundaryRegion ε) ∧
      ‖∫ p in NormalCrossing.boundaryRegion ε, circleFacePrimitive a u v r p‖ ≤
        primitiveFluxBound ε (uniformDeterminantBound (fun i : Fin n => a i.succ) D c)
          (logarithmBound (a 0) L) r := by
  apply circleFacePrimitive_flux_spec a u v j₀ ε
    (uniformDeterminantBound (fun i : Fin n => a i.succ) D c) L r hr
  · unfold uniformDeterminantBound exponentBound
    positivity
  · exact hF
  · exact hu
  · intro p hp i
    exact norm_pos_iff.mp (hc.trans_le (hunit p hp i))
  · exact hv₀
  · exact hvrest
  · intro p hp
    exact boundaryCoefficient_le_unitBounds (fun i : Fin n => a i.succ) (fun i => u i.succ)
      (v r p) (circleFacePoint r p) j₀ p.1 D c hc (hD p hp)
      (fun i => hunit p hp i.succ) (hv p hp)
  · exact hL

/-- The local normal-crossing primitive flux vanishes as its literal circle radius shrinks.
Uniform bounds are required only for radii in a fixed positive neighborhood of zero. -/
theorem tendsto_circleFacePrimitive_flux
    (a : Fin (n + 1) → Option J → ℤ) (u : Fin (n + 1) → (Option J → ℂ) → ℂ)
    (v : ℝ → (ℝ × (J → ℂ)) → Fin n → Option J → ℂ)
    (j₀ : Fin n) (ε : J → ℝ) (C L R : ℝ) (hR : 0 < R) (hC : 0 ≤ C)
    (hF : ∀ r ∈ Ioo 0 R, AEStronglyMeasurable (circleFacePrimitive a u v r)
      (volume.restrict (NormalCrossing.boundaryRegion ε)))
    (hu : ∀ r ∈ Ioo 0 R, ∀ p ∈ NormalCrossing.boundaryRegion ε, ∀ i,
      DifferentiableAt ℝ (u i) (circleFacePoint r p))
    (hu0 : ∀ r ∈ Ioo 0 R, ∀ p ∈ NormalCrossing.boundaryRegion ε, ∀ i,
      u i (circleFacePoint r p) ≠ 0)
    (hv₀ : ∀ r ∈ Ioo 0 R, ∀ p ∈ NormalCrossing.boundaryRegion ε,
      v r p j₀ = r • unitAngularTangent none p.1)
    (hvrest : ∀ r ∈ Ioo 0 R, ∀ p ∈ NormalCrossing.boundaryRegion ε, ∀ j,
      j ≠ j₀ → v r p j none = 0)
    (hcoeff : ∀ r ∈ Ioo 0 R, ∀ p ∈ NormalCrossing.boundaryRegion ε,
      boundaryCoefficient (fun i : Fin n => a i.succ) (fun i => u i.succ) (v r p)
        (circleFacePoint r p) j₀ p.1 ≤ C)
    (hL : ∀ r ∈ Ioo 0 R, ∀ p ∈ NormalCrossing.boundaryRegion ε,
      |Real.log ‖u 0 (circleFacePoint r p)‖| ≤ L) :
    Tendsto (fun r => ∫ p in NormalCrossing.boundaryRegion ε, circleFacePrimitive a u v r p)
      (𝓝[>] 0) (𝓝 0) := by
  apply squeeze_zero_norm' _ (tendsto_primitiveFluxBound ε C (logarithmBound (a 0) L))
  filter_upwards [Ioo_mem_nhdsGT hR] with r hr
  exact (circleFacePrimitive_flux_spec a u v j₀ ε C L r hr.1 hC (hF r hr)
    (hu r hr) (hu0 r hr) (hv₀ r hr) (hvrest r hr) (hcoeff r hr) (hL r hr)).2

end EnvelopingIsomorphism.Deformation.Kontsevich.LogMonomial
