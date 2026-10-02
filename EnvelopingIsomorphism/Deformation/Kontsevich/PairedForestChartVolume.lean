import EnvelopingIsomorphism.Deformation.Kontsevich.SimpleFaceNativeAtlas

/-! All auxiliary maps in the global native paired atlas preserve the literal
product volumes: canonical mark transport, integer phase translation, and the
coarse real-coordinate conversion. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestChartVolume
open SimpleFaceNativeAtlas SimpleProductPhaseIdentification InteriorGraphFaceCoordinates
open MeasureTheory BoxStokes
open scoped Classical

/-- The explicit interleaved Cartesian map is the existing graph basis map. -/
theorem coarse_eq_realCoordinates_symm (M m : ℕ) :
    (PlanarCoarseCartesian.coarse M m : _ → _) = (GraphForms.realCoordinates M m).symm := by
  have h : (PlanarCoarseCartesian.coarse M m).toLinearMap = (GraphForms.realCoordinates M m).symm.toLinearMap := by
    apply (Pi.basisFun ℝ (Fin (M * 2 + m))).ext
    intro j
    have hb : (Pi.basisFun ℝ (Fin (M * 2 + m))) j = standardBasis _ j := by
      ext k
      simp [Pi.basisFun_apply, standardBasis, Pi.single_apply]
    rw [hb]
    change PlanarCoarseCartesian.coarse M m (standardBasis _ j) = _
    rw [PlanarCoarseCartesian.coarse_standardBasis]
    apply (GraphForms.realCoordinates M m).injective
    change (GraphForms.realCoordinates M m) ((GraphForms.realBasis M m) j) =
      (GraphForms.realCoordinates M m) ((GraphForms.realCoordinates M m).symm (standardBasis _ j))
    rw [LinearEquiv.apply_symm_apply]
    ext k
    simp [GraphForms.realCoordinates, Module.Basis.equivFun_self, standardBasis, Pi.single_apply, eq_comm]
  exact congrArg (fun L : (Fin (M * 2 + m) → ℝ) →ₗ[ℝ] GraphForms.Coordinates M m ↦ (L : _ → _)) h

theorem volume_preserving_realCoordinates_symm (M m : ℕ) :
    MeasurePreserving ((GraphForms.realCoordinates M m).symm : _ → _) := by
  have h := PlanarCoarseCartesian.volume_preserving_coarse M m
  rw [PlanarCoarseCartesian.coarseMeas_eq, coarse_eq_realCoordinates_symm] at h
  exact h

variable {n m : ℕ} {i a b : Fin n} {S : Finset (Fin n)}
theorem volume_preserving_toProduct :
    MeasurePreserving (InteriorGraphFaceCoordinates.toProduct : RealProductCoordinates i a b S m → _) := by
  have h := (MeasurePreserving.id (volume : Measure (ShapeCoordinates a b S))).prod
    (volume_preserving_realCoordinates_symm (coarseN i a S) m)
  change MeasurePreserving (fun p : RealProductCoordinates i a b S m ↦
    (p.1, (GraphForms.realCoordinates (coarseN i a S) m).symm p.2))
  simpa only [← Measure.volume_eq_prod, Prod.map_def, id_eq] using h

variable {N r : ℕ} (hdim : GraphForms.dimension N m = r + 1)
  {a b : Fin (N + 1)} {T : Finset (Fin (N + 1))}

theorem volume_preserving_nativeEquiv (c : ChartIndex hdim a b T) :
    MeasurePreserving (nativeEquiv hdim c) := by
  rcases c with ⟨x, o, ho, z, hT, ha, hb, k⟩
  subst T; subst a; subst b
  exact MeasurePreserving.id _

theorem volume_preserving_shift (k : ℤ) :
    MeasurePreserving (shift k : ProductCoordinates (0 : Fin (N + 1)) a b T m → _) := by
  have h := ((measurePreserving_add_right (volume : Measure ℝ) ((k : ℝ) * (2 * Real.pi))).prod
    (MeasurePreserving.id (volume : Measure (InteriorFiberAngleSplit.Shape (shapeN a b T))))).prod
      (MeasurePreserving.id (volume : Measure (CoarseCoordinates (0 : Fin (N + 1)) a T m)))
  unfold shift
  simpa only [← Measure.volume_eq_prod, Prod.map_def, id_eq] using h

theorem volume_preserving_targetHomeomorph (c : ChartIndex hdim a b T) :
    MeasurePreserving (targetHomeomorph hdim c) :=
  (volume_preserving_shift c.turn).comp (volume_preserving_nativeEquiv hdim c)

/-- The common real product integral is exactly the original complex-product
integral after the canonical mark and phase change. -/
theorem integral_preimage_targetHomeomorph (c : ChartIndex hdim a b T)
    (f : ProductCoordinates 0 a b T m → ℝ) (s : Set (ProductCoordinates 0 a b T m)) :
    (∫ p in targetHomeomorph hdim c ⁻¹' s, f (targetHomeomorph hdim c p)) = ∫ p in s, f p :=
  (volume_preserving_targetHomeomorph hdim c).setIntegral_preimage_emb
    (targetHomeomorph hdim c).toMeasurableEquiv.measurableEmbedding f s

end EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestChartVolume
