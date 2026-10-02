import EnvelopingIsomorphism.Deformation.Kontsevich.ClusterInsertionJacobian

/-! The actual two-point angular/radial insertion and its boundary orientation. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.TwoPointInsertionJacobian

open scoped Matrix ContDiff
open ClusterInsertionJacobian

abbrev Angular := ClusterAngularCoordinates (0 : Fin 2) 0 1 Finset.univ 0
abbrev Index := ClusterAngularCoordinates.CoordinateIndex (0 : Fin 2) 0 1 Finset.univ 0

private instance : IsEmpty (ClusterCoarseIndex (0 : Fin 2) 0 Finset.univ) := by
  constructor
  rintro ⟨j, hj⟩
  simp at hj

private instance : IsEmpty (ClusterShapeIndex (0 : Fin 2) 1 Finset.univ) := by
  constructor
  rintro ⟨j, hj⟩
  fin_cases j <;> simp at hj

/-- These are actual native angular chart parameters; no free coarse or shape
coordinates remain for the two-point cluster containing the normalized anchor. -/
def parameters (p : ℝ × ℝ) : Angular := (0, 0, 0, p.1, p.2)

def coordinates : Angular ≃L[ℝ] ℝ × ℝ where
  toFun x := (x.2.2.2.1, x.2.2.2.2)
  invFun := parameters
  left_inv x := Prod.ext (Subsingleton.elim _ _)
    (Prod.ext (Subsingleton.elim _ _) (Prod.ext (Subsingleton.elim _ _) rfl))
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by unfold parameters; fun_prop

@[simp] theorem coordinates_apply (x : Angular) : coordinates x = (x.2.2.2.1, x.2.2.2.2) := rfl
@[simp] theorem coordinates_symm_apply (p : ℝ × ℝ) : coordinates.symm p = parameters p := rfl

/-- The position of the non-fixed vertex in the actual native insertion formula. -/
def nativeInsertion (x : Angular) : ℂ :=
  x.toFree.base (1 : Fin 2) + (x.toFree.radius : ℂ) * x.toFree.velocity 1

theorem nativeInsertion_eq (x : Angular) :
    nativeInsertion x = Complex.I + (x.2.2.2.2 : ℂ) * circleParameter x.2.2.2.1 := by
  simp [nativeInsertion, ClusterAngularCoordinates.toFree, ClusterFreeCoordinates.base,
    ClusterFreeCoordinates.representative, ClusterFreeCoordinates.velocity,
    ClusterFreeCoordinates.radius, circleParameter_eq]

/-- Native insertion expressed in the actual `(Re,Im)` target coordinates. -/
def realInsertion (p : ℝ × ℝ) : ℝ × ℝ :=
  Complex.equivRealProdCLM (nativeInsertion (coordinates.symm p))

theorem realInsertion_eq : realInsertion = polarInsertion (0, 1) := by
  funext p
  rw [realInsertion, nativeInsertion_eq]
  change Complex.equivRealProdCLM (Complex.I + (p.2 : ℂ) * circleParameter p.1) = polarInsertion (0, 1) p
  apply Prod.ext
  · change (Complex.I + (p.2 : ℂ) * circleParameter p.1).re = 0 + p.2 * Real.cos p.1
    simp [circleParameter, mul_comm Complex.I (p.1 : ℂ), Complex.exp_ofReal_mul_I_re]
  · change (Complex.I + (p.2 : ℂ) * circleParameter p.1).im = 1 + p.2 * Real.sin p.1
    simp [circleParameter, mul_comm Complex.I (p.1 : ℂ), Complex.exp_ofReal_mul_I_im]

theorem hasFDerivAt_realInsertion (p : ℝ × ℝ) :
    HasFDerivAt realInsertion (polarDerivative p) p := by
  rw [realInsertion_eq]
  exact hasFDerivAt_polarInsertion (0, 1) p

theorem det_fderiv_realInsertion (p : ℝ × ℝ) :
    LinearMap.det (fderiv ℝ realInsertion p).toLinearMap = -p.2 := by
  rw [realInsertion_eq]
  exact det_fderiv_polarInsertion (0, 1) p

theorem det_fderiv_realInsertion_neg (p : ℝ × ℝ) (hr : 0 < p.2) :
    LinearMap.det (fderiv ℝ realInsertion p).toLinearMap < 0 := by
  rw [det_fderiv_realInsertion]
  exact neg_neg_of_pos hr

theorem abs_det_fderiv_realInsertion (p : ℝ × ℝ) (hr : 0 < p.2) :
    |LinearMap.det (fderiv ℝ realInsertion p).toLinearMap| = p.2 := by
  rw [det_fderiv_realInsertion, abs_neg, abs_of_pos hr]

def angleIndex : Index := .inr (.inr (.inr (.inl ())))
def radiusIndex : Index := .inr (.inr (.inr (.inr ())))

/-- Explicit elimination of the empty coordinate blocks, preserving angle before radius. -/
def indexEquiv : Index ≃ Fin 2 where
  toFun
    | .inl x => isEmptyElim x
    | .inr (.inl x) => isEmptyElim x
    | .inr (.inr (.inl x)) => Fin.elim0 x
    | .inr (.inr (.inr (.inl _))) => 0
    | .inr (.inr (.inr (.inr _))) => 1
  invFun i := ![angleIndex, radiusIndex] i
  left_inv := by
    rintro (x | x | x | x | x)
    · exact isEmptyElim x
    · exact isEmptyElim x
    · exact Fin.elim0 x
    · cases x; rfl
    · cases x; rfl
  right_inv i := by fin_cases i <;> rfl

/-- The native chart basis really becomes the displayed `(angle,radius)` basis. -/
theorem coordinateBasis_map :
    ((ClusterAngularCoordinates.coordinateBasis (i := (0 : Fin 2)) (a := 0) (b := 1)
      (S := Finset.univ) (m := 0)).reindex indexEquiv).map coordinates.toLinearEquiv =
      Module.Basis.finTwoProd ℝ := by
  ext i <;> fin_cases i <;>
    simp [Module.Basis.map_apply, Module.Basis.reindex_apply, indexEquiv, angleIndex, radiusIndex,
      ClusterAngularCoordinates.coordinateBasis, coordinates]

/-- The outward radial vector and positive angular tangent, transported into
the actual native parameter space, have positive outward-first determinant. -/
theorem native_outward_angle_frame_det :
    ((ClusterAngularCoordinates.coordinateBasis (i := (0 : Fin 2)) (a := 0) (b := 1)
      (S := Finset.univ) (m := 0)).reindex indexEquiv).det
        ![coordinates.symm outwardNormal, coordinates.symm positiveAngleTangent] = 1 := by
  have h := outward_angle_frame_det
  rw [← coordinateBasis_map, Module.Basis.det_map] at h
  convert h using 1
  congr 1
  funext i
  fin_cases i <;> rfl

end EnvelopingIsomorphism.Deformation.Kontsevich.TwoPointInsertionJacobian
