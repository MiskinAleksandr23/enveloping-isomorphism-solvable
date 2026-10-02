import EnvelopingIsomorphism.Deformation.Kontsevich.OneVertexForms
import EnvelopingIsomorphism.Deformation.Kontsevich.OneVertexWeights
import EnvelopingIsomorphism.Deformation.Kontsevich.OneVertexHKR
import EnvelopingIsomorphism.Deformation.Kontsevich.OneVertexGraphOperators

/-!
# Actual one-vertex graph weights in arities zero through three

The integrals use the normalized real boundary-coordinate charts, their standard
orientation, and the actual determinant product of harmonic edge forms.
Kontsevich's factor `1/(m! (2π)^m)` is included for each labelled graph. Reordering
the outgoing labels changes the integral by its permutation sign.

Only arities `m < 4` are evaluated here. No higher-graph Stokes identity or
all-arity formality theorem is assumed.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Kontsevich

open MeasureTheory

/-- Integration in the normalized one-vertex charts of dimensions zero through three. -/
def oneVertexChartIntegral : (m : Fin 4) → ((Fin m.val → ℝ) → ℝ) → ℝ
  | ⟨0, _⟩, F => ∫ x : Fin 0 → ℝ, F x
  | ⟨1, _⟩, F => ∫ x : ℝ, F ![x]
  | ⟨2, _⟩, F => ∫ x : ℝ × ℝ in orderedPairSet, F ![x.1, x.2]
  | ⟨3, _⟩, F => ∫ x : ℝ × ℝ × ℝ in orderedTripleSet, F ![x.1, x.2.1, x.2.2]

/-- Absolute integrability in those same charts, independently of the integral's value. -/
def OneVertexChartIntegrable : (m : Fin 4) → ((Fin m.val → ℝ) → ℝ) → Prop
  | ⟨0, _⟩, F => Integrable F
  | ⟨1, _⟩, F => Integrable (fun x : ℝ => F ![x])
  | ⟨2, _⟩, F => IntegrableOn (fun x : ℝ × ℝ => F ![x.1, x.2]) orderedPairSet
  | ⟨3, _⟩, F => IntegrableOn (fun x : ℝ × ℝ × ℝ => F ![x.1, x.2.1, x.2.2]) orderedTripleSet

theorem oneVertexChartIntegral_const_mul (m : Fin 4) (c : ℝ) (F : (Fin m.val → ℝ) → ℝ) :
    oneVertexChartIntegral m (fun x => c * F x) = c * oneVertexChartIntegral m F := by
  fin_cases m <;> simp only [oneVertexChartIntegral, integral_const_mul]

theorem OneVertexChartIntegrable.const_mul (m : Fin 4) (c : ℝ)
    {F : (Fin m.val → ℝ) → ℝ} (hF : OneVertexChartIntegrable m F) :
    OneVertexChartIntegrable m (fun x => c * F x) := by
  fin_cases m <;> exact MeasureTheory.Integrable.const_mul hF c

theorem oneVertexTopForm_density {m : ℕ} (x : Fin m → ℝ) :
    oneVertexTopForm x (fun i => Pi.single i 1) = ∏ j : Fin m, edgeDensity (x j) :=
  oneVertexTopForm_coordinateBasis x

theorem oneVertexChartIntegrable_topForm (m : Fin 4) :
    OneVertexChartIntegrable m (fun x => oneVertexTopForm x (fun i => Pi.single i 1)) := by
  fin_cases m
  · dsimp [OneVertexChartIntegrable]
    simpa only [oneVertexTopForm_density, Fin.prod_univ_zero] using integrable_ordered_zero
  · dsimp [OneVertexChartIntegrable]
    simpa only [oneVertexTopForm_density, Fin.prod_univ_one, Matrix.cons_val_zero] using
      integrable_edgeDensity
  · dsimp [OneVertexChartIntegrable]
    simpa only [oneVertexTopForm_density, Fin.prod_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one] using integrableOn_ordered_two
  · dsimp [OneVertexChartIntegrable]
    simpa only [oneVertexTopForm_density, Fin.prod_univ_succ, Fin.prod_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.prod_univ_zero, mul_one] using
      integrableOn_ordered_three

/-- The actual unsigned integral of the ordered wedge of edge forms. -/
def oneVertexRawIntegral (m : Fin 4) : ℝ :=
  oneVertexChartIntegral m (fun x => oneVertexTopForm x (fun i => Pi.single i 1))

theorem oneVertexRawIntegral_zero : oneVertexRawIntegral 0 = 1 := by
  dsimp [oneVertexRawIntegral, oneVertexChartIntegral]
  simpa only [oneVertexTopForm_density, Fin.prod_univ_zero] using integral_ordered_zero

theorem oneVertexRawIntegral_one : oneVertexRawIntegral 1 = 2 * Real.pi := by
  dsimp [oneVertexRawIntegral, oneVertexChartIntegral]
  simpa only [oneVertexTopForm_density, Fin.prod_univ_one, Matrix.cons_val_zero] using integral_edgeDensity

theorem oneVertexRawIntegral_two : oneVertexRawIntegral 2 = (2 * Real.pi) ^ 2 / 2 := by
  dsimp [oneVertexRawIntegral, oneVertexChartIntegral]
  simpa only [oneVertexTopForm_density, Fin.prod_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one] using integral_ordered_two

theorem oneVertexRawIntegral_three : oneVertexRawIntegral 3 = (2 * Real.pi) ^ 3 / 6 := by
  dsimp [oneVertexRawIntegral, oneVertexChartIntegral]
  simpa only [oneVertexTopForm_density, Fin.prod_univ_succ, Fin.prod_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.prod_univ_zero, mul_one] using integral_ordered_three

/-- The geometric integrals have the factorial required by ordered boundary points. -/
theorem oneVertexRawIntegral_eq (m : Fin 4) :
    oneVertexRawIntegral m = (2 * Real.pi) ^ m.val / (m.val.factorial : ℝ) := by
  fin_cases m
  · simpa using oneVertexRawIntegral_zero
  · simpa using oneVertexRawIntegral_one
  · simpa using oneVertexRawIntegral_two
  · simpa [Nat.factorial] using oneVertexRawIntegral_three

/-- Integral with the outgoing-edge order specified by `σ`. -/
def labelledOneVertexRawIntegral (m : Fin 4) (σ : Equiv.Perm (Fin m.val)) : ℝ :=
  oneVertexChartIntegral m (fun x => permutedOneVertexTopForm σ x (fun i => Pi.single i 1))

theorem labelledOneVertexRawIntegral_eq (m : Fin 4) (σ : Equiv.Perm (Fin m.val)) :
    labelledOneVertexRawIntegral m σ = (Equiv.Perm.sign σ : ℝ) * oneVertexRawIntegral m := by
  simp only [labelledOneVertexRawIntegral, permutedOneVertexTopForm_eq,
    ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  exact oneVertexChartIntegral_const_mul m _ _

theorem oneVertexChartIntegrable_permutedTopForm (m : Fin 4) (σ : Equiv.Perm (Fin m.val)) :
    OneVertexChartIntegrable m
      (fun x => permutedOneVertexTopForm σ x (fun i => Pi.single i 1)) := by
  simp only [permutedOneVertexTopForm_eq, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  exact OneVertexChartIntegrable.const_mul m _ (oneVertexChartIntegrable_topForm m)

/-- The canonical labelled graph includes the outgoing-edge factorial, as in §6.2. -/
def canonicalOneVertexWeight (m : Fin 4) : ℝ :=
  (m.val.factorial : ℝ)⁻¹ * ((2 * Real.pi) ^ m.val)⁻¹ * oneVertexRawIntegral m

/-- Actual labelled weights, with the ordered form integrated before normalization. -/
def labelledOneVertexWeight (m : Fin 4) (σ : Equiv.Perm (Fin m.val)) : ℝ :=
  (m.val.factorial : ℝ)⁻¹ * ((2 * Real.pi) ^ m.val)⁻¹ * labelledOneVertexRawIntegral m σ

theorem canonicalOneVertexWeight_eq (m : Fin 4) :
    canonicalOneVertexWeight m = (m.val.factorial : ℝ)⁻¹ ^ 2 := by
  have hn : (m.val.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hp : (2 * Real.pi : ℝ) ≠ 0 := ne_of_gt (by positivity)
  rw [canonicalOneVertexWeight, oneVertexRawIntegral_eq]
  field_simp [hn, hp]

theorem labelledOneVertexWeight_eq (m : Fin 4) (σ : Equiv.Perm (Fin m.val)) :
    labelledOneVertexWeight m σ = (Equiv.Perm.sign σ : ℝ) * canonicalOneVertexWeight m := by
  rw [labelledOneVertexWeight, labelledOneVertexRawIntegral_eq, canonicalOneVertexWeight]
  ring

theorem canonicalOneVertexWeight_two : canonicalOneVertexWeight 2 = 1 / 4 := by
  rw [canonicalOneVertexWeight_eq]
  norm_num

theorem labelledOneVertexWeight_two_swap :
    labelledOneVertexWeight ⟨2, by decide⟩ (Equiv.swap (0 : Fin 2) (1 : Fin 2)) = -(1 / 4) := by
  rw [labelledOneVertexWeight_eq, canonicalOneVertexWeight_eq]
  norm_num [Nat.factorial]

section HKR

variable {K A : Type*} [Field K] [CharZero K] [Algebra ℝ K] [CommRing A] [Algebra K A]

/-- The finite one-vertex graph sum with actual real integral weights extended to `K`. -/
def geometricOneVertexSum (m : Fin 4) (a : A) (D : Fin m.val → Derivation K A A) :
    Cochain K A m.val :=
  ∑ σ : Equiv.Perm (Fin m.val),
    algebraMap ℝ K (labelledOneVertexWeight m σ) • oneVertexLabelledOperator σ a D

/-- In the verified arities, the actual integral weights give exactly the existing HKR map. -/
theorem geometricOneVertexSum_eq_hkr (m : Fin 4) (a : A)
    (D : Fin m.val → Derivation K A A) : geometricOneVertexSum m a D = hkrCochain a D := by
  rw [← oneVertexLabelledSum_factorial_eq_hkr a D]
  unfold geometricOneVertexSum oneVertexLabelledSum
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [labelledOneVertexWeight_eq, canonicalOneVertexWeight_eq]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
  · simp [hs]
  · simp [hs]
    exact neg_smul (((m.val.factorial : K) ^ 2)⁻¹) (oneVertexLabelledOperator σ a D)

end HKR

/-- The boundary-target bijection of an actual one-vertex `GraphDegree` graph. -/
def oneVertexGraphPermutation (Γ : KontsevichGraph 1) : Equiv.Perm (Fin 2) := by
  classical
  exact if Γ = forwardGraph then 1 else Equiv.swap 0 1

theorem oneVertexGraphPermutation_target (Γ : KontsevichGraph 1) (v : Fin 1) (a : Fin 2) :
    Γ.target (v, a) = Sum.inr (oneVertexGraphPermutation Γ a) := by
  rcases oneVertex_graph_cases Γ with rfl | rfl
  · simp only [oneVertexGraphPermutation]
    rfl
  · simp only [oneVertexGraphPermutation, if_neg (Ne.symm forwardGraph_ne_reverseGraph)]
    rfl

/-- Real integral weight attached to each of the actual two one-vertex graphs. -/
def geometricOneVertexGraphWeight (Γ : KontsevichGraph 1) : ℝ :=
  labelledOneVertexWeight ⟨2, by decide⟩ (oneVertexGraphPermutation Γ)

theorem geometricOneVertexGraphWeight_forward : geometricOneVertexGraphWeight forwardGraph = 1 / 4 := by
  simp only [geometricOneVertexGraphWeight, oneVertexGraphPermutation]
  rw [labelledOneVertexWeight_eq, canonicalOneVertexWeight_eq]
  norm_num [Nat.factorial]

theorem geometricOneVertexGraphWeight_reverse : geometricOneVertexGraphWeight reverseGraph = -1 / 4 := by
  simp only [geometricOneVertexGraphWeight, oneVertexGraphPermutation,
    if_neg (Ne.symm forwardGraph_ne_reverseGraph)]
  simpa only [neg_div] using labelledOneVertexWeight_two_swap

/-- The actual geometric integral weights supply the normalized first graph coefficient. -/
theorem weightedOperator_oneVertex_geometric {K : Type*} [Field K] [CharZero K] [Algebra ℝ K]
    {d : ℕ} (c : Fin d → Fin d → Fin d → K) (hc : KontsevichGraph.IsSkew c) :
    KontsevichGraph.weightedOperator Finset.univ
      (fun Γ => algebraMap ℝ K (geometricOneVertexGraphWeight Γ)) (fun _ => c) =
      (1 / 2 : K) • linearPoissonBinary c := by
  apply weightedOperator_oneVertex_of_values _ _ _ c hc
  · rw [geometricOneVertexGraphWeight_forward]
    simp only [map_div₀, map_one, map_ofNat]
  · rw [geometricOneVertexGraphWeight_reverse]
    simp only [map_div₀, map_neg, map_one, map_ofNat]

end EnvelopingIsomorphism.Deformation.Kontsevich
