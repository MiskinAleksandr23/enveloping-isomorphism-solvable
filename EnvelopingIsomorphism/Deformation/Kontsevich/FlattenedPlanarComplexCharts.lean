import EnvelopingIsomorphism.Deformation.Kontsevich.FinitePlanarComplexChartCover

/-! The actual independent normal and free forest entries, enumerated by Fin N. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.FlattenedPlanarComplexCharts
open Configuration InteriorFiberAngleSplit PlanarComplexForestCharts
open FinitePlanarComplexChartCover
open scoped Classical BigOperators Topology
variable {N : ℕ} (c : CompactPlanar N)

abbrev Normal := PlanarComplexForestCharts.Normal 0 (fiberPoint c).val (fiberPoint c).property
abbrev Free := ComplexForestFreeShapes.Free (upperTree 0 (fiberPoint c).val (fiberPoint c).property)
  (marks 0 (fiberPoint c).val (fiberPoint c).property)
abbrev Index := Normal c ⊕ Free c

theorem card_index : Fintype.card (Index c) = N := by
  have h := complex_dimension 0 (fiberPoint c).val (fiberPoint c).property
  simpa only [Coordinates, ComplexForestFreeShapes.Coordinates, Module.finrank_prod,
    Module.finrank_pi_fintype, Module.finrank_self, Finset.sum_const, Finset.card_univ,
    smul_eq_mul, mul_one, Index, Fintype.card_sum] using h

def indexEquiv : Index c ≃ Fin N := Fintype.equivFinOfCardEq (card_index c)

def unflatten : Shape N ≃L[ℂ] LocalCoordinates c :=
  (ContinuousLinearEquiv.piCongrLeft ℂ (fun _ : Index c ↦ ℂ) (indexEquiv c).symm).trans
    (ContinuousLinearEquiv.sumPiEquivProdPi ℂ (Normal c) (Free c) (fun _ ↦ ℂ))

@[simp] theorem unflatten_normal (z : Shape N) (v : Normal c) :
    (unflatten c z).1 v = z (indexEquiv c (Sum.inl v)) := by
  simp [unflatten, ContinuousLinearEquiv.piCongrLeft,
    ContinuousLinearEquiv.sumPiEquivProdPi, Equiv.piCongrLeft]
@[simp] theorem unflatten_free (z : Shape N) (v : Free c) :
    (unflatten c z).2 v = z (indexEquiv c (Sum.inr v)) := by
  simp [unflatten, ContinuousLinearEquiv.piCongrLeft,
    ContinuousLinearEquiv.sumPiEquivProdPi, Equiv.piCongrLeft]

def domain : Set (Shape N) := unflatten c ⁻¹' domainAt c

def chart : Shape N → Shape N := chartAt c ∘ unflatten c

def exponent (j k b d : Point N) (i : Fin N) : ℤ :=
  Sum.elim (PlanarComplexForestCharts.exponent 0 (fiberPoint c).val (fiberPoint c).property j k b d)
    (fun _ ↦ 0) ((indexEquiv c).symm i)

def unit (j k b d : Point N) : Shape N → ℂ :=
  PlanarComplexForestCharts.unit 0 (fiberPoint c).val (fiberPoint c).property j k b d ∘ unflatten c

theorem isOpen_domain : IsOpen (domain c) := (isOpen_domainAt c).preimage (unflatten c).continuous

theorem isBounded_domain : Bornology.IsBounded (domain c) := by
  have he : domain c = (unflatten c).symm '' domainAt c := by
    ext z
    constructor
    · intro hz; exact ⟨unflatten c z, hz, (unflatten c).symm_apply_apply z⟩
    · rintro ⟨y, hy, rfl⟩; simpa [domain] using hy
  rw [he]
  exact (unflatten c).symm.lipschitz.isBounded_image (isBounded_domainAt c)

theorem domain_coordinates_ne_zero {z : Shape N} (hz : z ∈ domain c) : ∀ i, z i ≠ 0 := by
  intro i
  obtain ⟨v, rfl⟩ := (indexEquiv c).surjective i
  cases v with
  | inl v => simpa only [ComplexForestFreeShapes.parameters, unflatten_normal] using hz.2.2 v
  | inr v => simpa only [← unflatten_free] using BoundedPlanarComplexCharts.ball_subset_freeLocus _ _ _ hz.1 v

theorem chart_image : chart c '' domain c = chartAt c '' domainAt c := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨unflatten c y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    refine ⟨(unflatten c).symm y, ?_, ?_⟩
    · simpa [domain] using hy
    · simp [chart]

theorem chart_injOn : Set.InjOn (chart c) (domain c) :=
  fun _ hx _ hy h ↦ (unflatten c).injective (chartAt_injOn c hx hy h)

theorem isOpen_chart_image : IsOpen (chart c '' domain c) := by
  rw [chart_image]; exact isOpen_image_chartAt c

theorem chart_mapsTo : Set.MapsTo (chart c) (domain c) (shapeConfiguration N) :=
  fun _ hz ↦ chartAt_mapsTo_configuration c hz

theorem analyticOnNhd_chart : AnalyticOnNhd ℂ (chart c) (domain c) :=
  fun _ hz ↦ (analyticOnNhd_chartAt c _ hz).comp ((unflatten c).analyticAt _)

theorem product_exponent (j k b d : Point N) (z : Shape N) :
    (∏ i, z i ^ exponent c j k b d i) =
      ∏ v : Normal c, (unflatten c z).1 v ^
        PlanarComplexForestCharts.exponent 0 (fiberPoint c).val (fiberPoint c).property j k b d v := by
  rw [← Equiv.prod_comp (indexEquiv c)]
  simp [exponent, Fintype.prod_sum_type]

theorem pairRatio_monomial {z : Shape N} (hz : z ∈ domain c)
    (j k b d : Point N) (hjk : j ≠ k) (hbd : b ≠ d) :
    shapeDifference j k (chart c z) / shapeDifference b d (chart c z) =
      (∏ i, z i ^ exponent c j k b d i) * unit c j k b d z := by
  rw [product_exponent]
  exact chartAt_pairRatio_monomial c hz j k b d hjk hbd

theorem pairDifference_monomial {z : Shape N} (hz : z ∈ domain c)
    (j k : Point N) (hjk : j ≠ k) :
    shapeDifference j k (chart c z) =
      (∏ i, z i ^ exponent c j k 0 1 i) * unit c j k 0 1 z := by
  simpa [shapeDifference] using pairRatio_monomial c hz j k 0 1 hjk Fin.zero_ne_one

theorem analyticOnNhd_unit (j k b d : Point N) (hjk : j ≠ k) (hbd : b ≠ d) :
    AnalyticOnNhd ℂ (unit c j k b d) (domain c) := by
  intro z hz
  exact ((ComplexForestFreeShapes.analyticOnNhd_unit _ _ _ j k b d hjk hbd) _
    (BoundedPlanarComplexCharts.ball_subset_unitLocus _ _ _ hz.1)).comp ((unflatten c).analyticAt z)

theorem unit_ne_zero (j k b d : Point N) (hjk : j ≠ k) (hbd : b ≠ d)
    {z : Shape N} (hz : z ∈ domain c) : unit c j k b d z ≠ 0 :=
  ComplexForestNormalizedCharts.unit_ne_zero _ _
    (BoundedPlanarComplexCharts.ball_subset_unitLocus _ _ _ hz.1) j k b d hjk hbd

theorem uniform_unit_bounds (j k b d : Point N) (hjk : j ≠ k) (hbd : b ≠ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ domain c,
      ‖unit c j k b d z‖ ≤ C ∧ ‖(unit c j k b d z)⁻¹‖ ≤ C ∧
      ‖fderiv ℝ (unit c j k b d) z‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ := local_uniform_unit_bounds c j k b d hjk hbd
  let L := (unflatten c).toContinuousLinearMap
  refine ⟨C * (1 + ‖L‖), mul_pos hC (by positivity), fun z hz ↦ ?_⟩
  have hle : C ≤ C * (1 + ‖L‖) := by nlinarith [norm_nonneg L]
  have ha := (ComplexForestFreeShapes.analyticOnNhd_unit _ _ _ j k b d hjk hbd) _
    (BoundedPlanarComplexCharts.ball_subset_unitLocus _ _ _ hz.1)
  have hd : fderiv ℂ (unit c j k b d) z =
      (fderiv ℂ (PlanarComplexForestCharts.unit 0 (fiberPoint c).val (fiberPoint c).property j k b d)
        (unflatten c z)).comp L :=
    (ha.differentiableAt.hasFDerivAt.comp z (unflatten c).hasFDerivAt).fderiv
  have hb := hbound (unflatten c z) hz
  refine ⟨hb.1.trans hle, hb.2.1.trans hle, ?_⟩
  rw [((analyticOnNhd_unit c j k b d hjk hbd) z hz).differentiableAt.fderiv_restrictScalars ℝ,
    ContinuousLinearMap.norm_restrictScalars, hd]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul_of_nonneg_right hb.2.2 (norm_nonneg L)).trans (by nlinarith [norm_nonneg L]))

theorem finite_cover : ∃ centers : Finset (CompactPlanar N),
    shapeConfiguration N ⊆ ⋃ c ∈ centers, chart c '' domain c := by
  obtain ⟨s, hs⟩ := finite_complex_cover (N := N)
  refine ⟨s, fun z hz ↦ ?_⟩
  obtain ⟨c, hc, h⟩ := hs ⟨z, hz⟩
  exact Set.mem_iUnion.mpr ⟨c, Set.mem_iUnion.mpr ⟨hc, (chart_image c).symm ▸ h⟩⟩

end EnvelopingIsomorphism.Deformation.Kontsevich.FlattenedPlanarComplexCharts
