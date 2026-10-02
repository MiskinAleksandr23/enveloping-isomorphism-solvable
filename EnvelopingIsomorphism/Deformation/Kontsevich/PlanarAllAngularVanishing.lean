import EnvelopingIsomorphism.Deformation.Kontsevich.PlanarAngularVanishing

/-! Arbitrary ordered angular forms in the existing fixed planar marks.
Expanding the actual angle row reduces to the already constructed exact
shape primitives, so no change of normalization measure is required. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Kontsevich.PlanarAllAngularVanishing
open InteriorFiberAngleSplit PlanarOrderedAngularForms Set MeasureTheory
open scoped BigOperators

def minor {N : ℕ} (e : OrderedEdges N) (j : Fin (Dim N + 1)) : InteriorFiberAngleSplit.Edges N :=
  fun k ↦ e (j.succAbove k)

theorem rotatedEdgeForm_angle {N : ℕ} (s t : Point N) (hst : s ≠ t)
    (x : Parameters N) (hx : x.2 ∈ shapeConfiguration N) :
    rotatedEdgeForm s t x (fun _ : Fin 1 ↦ (1, 0)) = 1 := by
  rw [rotatedEdgeForm_split_on_configuration x hx s t hst]
  simp only [ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.compContinuousLinearMap_apply]
  change 1 + shapeEdgeForm s t x.2 (fun _ ↦ 0) = 1
  simp [shapeEdgeForm, angularForm_apply]

/-- Exact Laplace expansion of the original density, including every column sign. -/
theorem density_eq_sum {N : ℕ} (e : OrderedEdges N) (he : ∀ j, (e j).1 ≠ (e j).2)
    (x : Parameters N) (hx : x.2 ∈ shapeConfiguration N) :
    density e (Equiv.refl _) x = ∑ j : Fin (Dim N + 1),
      (-1 : ℝ) ^ j.val * fiberDensity (minor e j) x := by
  rw [density_eq_det, Matrix.det_succ_row_zero]
  apply Finset.sum_congr rfl
  intro j _
  have hangle : relabeledEdgeForm (Equiv.refl (Point N)) (e j).1 (e j).2 x
      (fun _ ↦ fiberFrame N 0) = 1 := rotatedEdgeForm_angle _ _ (he j) x hx
  rw [hangle, mul_one, fiberDensity_eq_shapeDensity, shapeDensity_eq_det]
  congr 1
  congr 1
  funext r c
  exact rotatedEdgeForm_horizontal _ _ x (AngularRadial.realBasis N r)

/-- L1 and zero integral for any ordered angular list in the fixed original
marks. This does not assume the first edge is the normalization reference. -/
theorem integral_eq_zero {N : ℕ} (e : OrderedEdges (N + 1)) :
    IntegrableOn (density e (Equiv.refl _)) (integrationRegion (N + 1)) ∧
      (∫ x in integrationRegion (N + 1), density e (Equiv.refl _) x) = 0 := by
  classical
  by_cases he : ∀ j, (e j).1 ≠ (e j).2
  · have hminor (j : Fin (Dim (N + 1) + 1)) :=
      PlanarAngularVanishing.integral_fiberDensity_eq_zero (primitiveEdges (minor e j))
        (primitiveEdges_nonloop _ (fun k ↦ he (j.succAbove k)))
    simp only [angularEdges_primitiveEdges] at hminor
    have hi (j : Fin (Dim (N + 1) + 1)) : IntegrableOn
        (fun x ↦ (-1 : ℝ) ^ j.val * fiberDensity (minor e j) x) (integrationRegion (N + 1)) :=
      (hminor j).1.const_mul _
    have heq : ∀ x ∈ integrationRegion (N + 1), density e (Equiv.refl _) x =
        ∑ j : Fin (Dim (N + 1) + 1), (-1 : ℝ) ^ j.val * fiberDensity (minor e j) x :=
      fun x hx ↦ density_eq_sum e he x hx.2
    refine ⟨?_, ?_⟩
    · have hsum : IntegrableOn (fun x ↦ ∑ j : Fin (Dim (N + 1) + 1),
          (-1 : ℝ) ^ j.val * fiberDensity (minor e j) x) (integrationRegion (N + 1)) :=
          integrable_finsetSum _ (fun j _ ↦ hi j)
      exact hsum.congr_fun (fun x hx ↦ (heq x hx).symm) (measurableSet_integrationRegion _)
    · rw [setIntegral_congr_fun (measurableSet_integrationRegion _) heq,
        integral_finsetSum _ (fun j _ ↦ hi j)]
      simp_rw [integral_const_mul, (hminor _).2, mul_zero]
      simp
  · push Not at he
    obtain ⟨j, hj⟩ := he
    have hz : density e (Equiv.refl _) = 0 := funext (density_eq_zero_of_loop e _ j hj)
    rw [hz]
    exact ⟨integrableOn_zero, by simp⟩

end EnvelopingIsomorphism.Deformation.Kontsevich.PlanarAllAngularVanishing
