import EnvelopingIsomorphism.Deformation.Kontsevich.NormalCrossingStokes
import EnvelopingIsomorphism.Deformation.Kontsevich.LogMonomialBoundaryPrimitive

/-! Genuine conversion from simultaneous polar radial faces to circle × complex
remaining-coordinate integrals, preserving the inherited face orientation. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Kontsevich.NormalCrossingCylinderCoordinates

open Set MeasureTheory ContinuousAlternatingMap Filter
open BoxStokes NormalCrossingStokes
open scoped Topology

abbrev MixedCart (N : ℕ) := ℝ × (Fin N → ℝ × ℝ)
abbrev MixedComplex (N : ℕ) := ℝ × (Fin N → ℂ)

local instance (N : ℕ) : (volume : Measure (MixedCart N)).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure _ _

def mixedCLM {N : ℕ} (i : Fin (N + 1)) : Coord (Degree N) →L[ℝ] MixedCart N :=
  (((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.proj i)).comp
    ((split N).toContinuousLinearMap.comp (faceTangent (radiusIndex i)))).prod
  (ContinuousLinearMap.pi fun k ↦ (ContinuousLinearMap.proj (i.succAbove k)).comp
    ((split N).toContinuousLinearMap.comp (faceTangent (radiusIndex i))))

def fullCoordinates {N : ℕ} (i : Fin (N + 1)) :
    (ℝ × Coord (Degree N)) ≃ᵐ (ℝ × MixedCart N) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (Dim N) ↦ ℝ) (radiusIndex i)).symm.trans
    ((splitMeas N).trans
      ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N + 1) ↦ ℝ × ℝ) i).trans
        MeasurableEquiv.prodAssoc))

theorem volume_preserving_fullCoordinates {N : ℕ} (i : Fin (N + 1)) :
    MeasurePreserving (fullCoordinates i) :=
  volume_preserving_prodAssoc.comp
    ((volume_preserving_piFinSuccAbove (fun _ : Fin (N + 1) ↦ ℝ × ℝ) i).comp
      ((volume_preserving_split N).comp
        ((volume_preserving_piFinSuccAbove (fun _ : Fin (Dim N) ↦ ℝ) (radiusIndex i)).symm _)))

theorem fullCoordinates_apply {N : ℕ} (i : Fin (N + 1)) (r : ℝ) (x : Coord (Degree N)) :
    fullCoordinates i (r, x) = (r, mixedCLM i x) := by
  change ((split N ((radiusIndex i).insertNth r x) i).1,
    ((split N ((radiusIndex i).insertNth r x) i).2,
      i.removeNth (split N ((radiusIndex i).insertNth r x)))) = _
  apply Prod.ext
  · simp only [split_apply, Fin.insertNth_apply_same]
  · apply Prod.ext
    · change faceEmbedding (radiusIndex i) r x (angleIndex i) =
        faceEmbedding (radiusIndex i) 0 x (angleIndex i)
      exact faceEmbedding_other_eq _ _ r 0 x (angleIndex_ne_radiusIndex i i)
    · funext k
      apply Prod.ext
      · change faceEmbedding (radiusIndex i) r x (radiusIndex (i.succAbove k)) =
          faceEmbedding (radiusIndex i) 0 x (radiusIndex (i.succAbove k))
        exact faceEmbedding_other_eq _ _ r 0 x (by simp)
      · change faceEmbedding (radiusIndex i) r x (angleIndex (i.succAbove k)) =
          faceEmbedding (radiusIndex i) 0 x (angleIndex (i.succAbove k))
        exact faceEmbedding_other_eq _ _ r 0 x (by simp)

theorem mixedCLM_bijective {N : ℕ} (i : Fin (N + 1)) : Function.Bijective (mixedCLM i) := by
  constructor
  · intro x y h
    have hh : fullCoordinates i (0, x) = fullCoordinates i (0, y) := by
      rw [fullCoordinates_apply, fullCoordinates_apply, h]
    exact congrArg Prod.snd ((fullCoordinates i).injective hh)
  · intro p
    obtain ⟨q, hq⟩ := (fullCoordinates i).surjective (0, p)
    rcases q with ⟨a, y⟩
    rw [fullCoordinates_apply] at hq
    exact ⟨y, congrArg Prod.snd hq⟩

def mixedEquiv {N : ℕ} (i : Fin (N + 1)) : Coord (Degree N) ≃L[ℝ] MixedCart N :=
  (LinearEquiv.ofBijective (mixedCLM i).toLinearMap (mixedCLM_bijective i)).toContinuousLinearEquiv

def mixedMeas {N : ℕ} (i : Fin (N + 1)) : Coord (Degree N) ≃ᵐ MixedCart N :=
  (mixedEquiv i).toHomeomorph.toMeasurableEquiv

theorem mixedEquiv_apply {N : ℕ} (i : Fin (N + 1)) (x : Coord (Degree N)) :
    mixedEquiv i x = mixedCLM i x := rfl

theorem mixedMeas_apply {N : ℕ} (i : Fin (N + 1)) (x : Coord (Degree N)) :
    mixedMeas i x = mixedCLM i x := rfl

/-- Removing the distinguished radial coordinate preserves actual face volume.
This is deduced from the ambient product equivalence on a radial interval of volume one. -/
theorem volume_preserving_mixedMeas {N : ℕ} (i : Fin (N + 1)) : MeasurePreserving (mixedMeas i) := by
  refine ⟨(mixedMeas i).measurable, ?_⟩
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (mixedMeas i).measurable hs]
  have h := (volume_preserving_fullCoordinates i).measure_preimage
    (measurableSet_Ioc.prod hs).nullMeasurableSet (s := Ioc (0 : ℝ) 1 ×ˢ s)
  have heq : fullCoordinates i ⁻¹' (Ioc (0 : ℝ) 1 ×ˢ s) =
      Ioc (0 : ℝ) 1 ×ˢ ((mixedMeas i) ⁻¹' s) := by
    ext ⟨a, y⟩
    rw [mem_preimage, fullCoordinates_apply]
    rfl
  rw [heq] at h
  simp only [Measure.volume_eq_prod, Measure.prod_prod] at h
  simpa only [Real.volume_Ioc, sub_zero, ENNReal.ofReal_one, one_mul, ← Measure.volume_eq_prod] using h

def otherConvert (N : ℕ) : (Fin N → ℝ × ℝ) →L[ℝ] (Fin N → ℂ) :=
  ContinuousLinearMap.pi (fun k ↦ Complex.equivRealProdCLM.symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.proj k))

def mixedConvert (N : ℕ) : MixedCart N →L[ℝ] MixedComplex N :=
  (ContinuousLinearMap.id ℝ ℝ).prodMap (otherConvert N)

def mixedPolar {N : ℕ} (p : MixedCart N) : MixedComplex N :=
  (p.1, fun k ↦ Complex.polarCoord.symm (p.2 k))

def mixedRealDerivative {N : ℕ} (p : MixedCart N) : MixedCart N →L[ℝ] MixedCart N :=
  (ContinuousLinearMap.id ℝ ℝ).prodMap (fderivPiPolarCoordSymm p.2)

theorem hasFDerivAt_mixedPolar {N : ℕ} (p : MixedCart N) :
    HasFDerivAt mixedPolar ((mixedConvert N).comp (mixedRealDerivative p)) p := by
  have h := (mixedConvert N).hasFDerivAt.comp p
    ((ContinuousLinearMap.fst ℝ ℝ (Fin N → ℝ × ℝ)).hasFDerivAt.prodMk
      ((hasFDerivAt_pi_polarCoord_symm p.2).comp p
        (ContinuousLinearMap.snd ℝ ℝ (Fin N → ℝ × ℝ)).hasFDerivAt))
  exact h

theorem det_mixedRealDerivative {N : ℕ} (p : MixedCart N) :
    (mixedRealDerivative p).det = ∏ k : Fin N, (p.2 k).1 := by
  change LinearMap.det ((LinearMap.id : ℝ →ₗ[ℝ] ℝ).prodMap (fderivPiPolarCoordSymm p.2).toLinearMap) = _
  rw [LinearMap.det_prodMap, LinearMap.det_id, one_mul]
  exact det_fderivPiPolarCoordSymm p.2

/-- Ordinary circle × complex-remaining-coordinate parametrization at any normal i. -/
def nativeCylinder {N : ℕ} (i : Fin (N + 1)) (r : ℝ) (p : MixedComplex N) : Space N :=
  i.insertNth (LogCircle.shrinkingCircle r p.1) p.2

def nativeDerivative {N : ℕ} (i : Fin (N + 1)) (r : ℝ) (p : MixedComplex N) :
    MixedComplex N →L[ℝ] Space N :=
  ContinuousLinearMap.pi (i.insertNth
    ((LogCircle.shrinkingCircleTangent r p.1).comp (ContinuousLinearMap.fst ℝ ℝ (Fin N → ℂ)))
    (fun k ↦ (ContinuousLinearMap.proj k).comp (ContinuousLinearMap.snd ℝ ℝ (Fin N → ℂ))))

theorem hasFDerivAt_nativeCylinder {N : ℕ} (i : Fin (N + 1)) (r : ℝ) (p : MixedComplex N) :
    HasFDerivAt (nativeCylinder i r) (nativeDerivative i r p) p := by
  apply hasFDerivAt_pi.mpr
  intro k
  induction k using i.succAboveCases with
  | x =>
    simpa only [nativeCylinder, nativeDerivative, ContinuousLinearMap.pi_apply, Fin.insertNth_apply_same, Function.comp_def] using
      (LogCircle.hasFDerivAt_shrinkingCircle r p.1).comp p
        (ContinuousLinearMap.fst ℝ ℝ (Fin N → ℂ)).hasFDerivAt
  | p k =>
    simp only [nativeCylinder, Fin.insertNth_apply_succAbove]
    convert (((ContinuousLinearMap.proj k : (Fin N → ℂ) →L[ℝ] ℂ).comp
      (ContinuousLinearMap.snd ℝ ℝ (Fin N → ℂ))).hasFDerivAt (x := p)) using 1 <;> rfl

theorem split_fullFace {N : ℕ} (i : Fin (N + 1)) (r : ℝ) (x : Coord (Degree N)) :
    split N (faceEmbedding (radiusIndex i) r x) =
      i.insertNth (r, (mixedCLM i x).1) (mixedCLM i x).2 := by
  have h := fullCoordinates_apply i r x
  change ((split N (faceEmbedding (radiusIndex i) r x) i).1,
      ((split N (faceEmbedding (radiusIndex i) r x) i).2,
        i.removeNth (split N (faceEmbedding (radiusIndex i) r x)))) = (r, mixedCLM i x) at h
  have hr := congrArg Prod.fst h
  have ht := congrArg (fun p : ℝ × MixedCart N ↦ p.2.1) h
  have ho := congrArg (fun p : ℝ × MixedCart N ↦ p.2.2) h
  funext k
  induction k using i.succAboveCases with
  | x =>
    rw [Fin.insertNth_apply_same]
    apply Prod.ext
    · exact hr
    · exact ht
  | p k => simpa only [Fin.insertNth_apply_succAbove, Fin.removeNth] using congrFun ho k

theorem cylinder_factorization {N : ℕ} (i : Fin (N + 1)) (r : ℝ) :
    NormalCrossingStokes.cylinder i r = nativeCylinder i r ∘ mixedPolar ∘ mixedEquiv i := by
  funext x
  rw [NormalCrossingStokes.cylinder, polar_eq_native, split_fullFace]
  funext k
  induction k using i.succAboveCases with
  | x =>
    simp only [Fin.insertNth_apply_same, Function.comp_apply, nativeCylinder, mixedPolar, mixedEquiv_apply]
    exact (PuncturedCoordinateStokes.polar_eq_native ![r, (mixedCLM i x).1]).symm
  | p k =>
    simp only [Fin.insertNth_apply_succAbove, Function.comp_apply, nativeCylinder, mixedPolar, mixedEquiv_apply]

/-- The inherited Stokes column order, now represented in circle × complex coordinates. -/
def mixedFrame {N : ℕ} (i : Fin (N + 1)) : Fin (Degree N) → MixedComplex N :=
  (mixedConvert N : MixedCart N → MixedComplex N) ∘ (mixedEquiv i : Coord (Degree N) → MixedCart N) ∘
    standardBasis (Degree N)

def nativeDensity {N : ℕ} (ω : CrossingForm N) (i : Fin (N + 1)) (r : ℝ) (p : MixedComplex N) : ℝ :=
  (ω (nativeCylinder i r p)).compContinuousLinearMap (fderiv ℝ (nativeCylinder i r) p) (mixedFrame i)

theorem topForm_mixedPolar {N : ℕ} (α : MixedComplex N [⋀^Fin (Degree N)]→L[ℝ] ℝ)
    (i : Fin (N + 1)) (x : Coord (Degree N)) :
    α (((mixedConvert N).comp ((mixedRealDerivative (mixedEquiv i x)).comp
      (mixedEquiv i).toContinuousLinearMap) : Coord (Degree N) → MixedComplex N) ∘ standardBasis (Degree N)) =
      (∏ k : Fin N, ((mixedEquiv i x).2 k).1) * α (mixedFrame i) := by
  let b := (Pi.basisFun ℝ (Fin (Degree N))).map (mixedEquiv i).toLinearEquiv
  let β := α.toAlternatingMap.compLinearMap (mixedConvert N).toLinearMap
  have hb : (b : Fin (Degree N) → MixedCart N) =
      (mixedEquiv i : Coord (Degree N) → MixedCart N) ∘ standardBasis (Degree N) := by
    funext j
    simp [b, standardBasis, Pi.basisFun_apply]
  change β ((mixedRealDerivative (mixedEquiv i x) : MixedCart N → MixedCart N) ∘
    ((mixedEquiv i : Coord (Degree N) → MixedCart N) ∘ standardBasis (Degree N))) = _
  rw [← hb]
  have he := β.eq_smul_basis_det b
  have hh := congrArg (fun γ : MixedCart N [⋀^Fin (Degree N)]→ₗ[ℝ] ℝ ↦
    γ ((mixedRealDerivative (mixedEquiv i x) : MixedCart N → MixedCart N) ∘ b)) he
  simp only [AlternatingMap.smul_apply, smul_eq_mul] at hh
  have hdet := b.det_comp (mixedRealDerivative (mixedEquiv i x)).toLinearMap b
  simp only [ContinuousLinearMap.coe_coe, b.det_self, mul_one] at hdet
  have hJ : LinearMap.det (mixedRealDerivative (mixedEquiv i x)).toLinearMap =
      ∏ k : Fin N, ((mixedEquiv i x).2 k).1 := det_mixedRealDerivative (mixedEquiv i x)
  rw [hdet, hJ] at hh
  rw [hh, mul_comm]
  congr 1
  rw [hb]
  rfl

/-- The actual face coefficient gains precisely the product of the remaining radii. -/
theorem cylinderDensity_eq_jacobian {N : ℕ} (ω : CrossingForm N) (i : Fin (N + 1))
    (r : ℝ) (x : Coord (Degree N)) :
    NormalCrossingStokes.cylinderDensity ω i r x =
      (∏ k : Fin N, ((mixedEquiv i x).2 k).1) * nativeDensity ω i r (mixedPolar (mixedEquiv i x)) := by
  have hd := (hasFDerivAt_nativeCylinder i r (mixedPolar (mixedEquiv i x))).comp x
    ((hasFDerivAt_mixedPolar (mixedEquiv i x)).comp x (mixedEquiv i).hasFDerivAt)
  rw [← cylinder_factorization] at hd
  rw [NormalCrossingStokes.cylinderDensity, hd.fderiv, cylinder_factorization]
  unfold nativeDensity
  rw [(hasFDerivAt_nativeCylinder i r _).fderiv]
  exact topForm_mixedPolar
    ((ω (nativeCylinder i r (mixedPolar (mixedEquiv i x)))).compContinuousLinearMap
      (nativeDerivative i r (mixedPolar (mixedEquiv i x)))) i x

def mixedRealPolar {N : ℕ} (p : MixedCart N) : MixedCart N :=
  (p.1, fun k ↦ polarCoord.symm (p.2 k))

def mixedTarget (N : ℕ) : Set (MixedCart N) :=
  univ ×ˢ univ.pi (fun _ ↦ polarCoord.target)

theorem hasFDerivAt_mixedRealPolar {N : ℕ} (p : MixedCart N) :
    HasFDerivAt mixedRealPolar (mixedRealDerivative p) p :=
  (ContinuousLinearMap.fst ℝ ℝ (Fin N → ℝ × ℝ)).hasFDerivAt.prodMk
    ((hasFDerivAt_pi_polarCoord_symm p.2).comp p
      (ContinuousLinearMap.snd ℝ ℝ (Fin N → ℝ × ℝ)).hasFDerivAt)

theorem measurableSet_mixedTarget (N : ℕ) : MeasurableSet (mixedTarget N) :=
  (MeasurableSet.univ : MeasurableSet (univ : Set ℝ)).prod measurableSet_pi_polarCoord_target

theorem injOn_mixedRealPolar (N : ℕ) : InjOn (@mixedRealPolar N) (mixedTarget N) := by
  intro p hp q hq h
  apply Prod.ext
  · have hfst := congrArg (fun t : MixedCart N ↦ t.1) h
    exact hfst
  · exact injOn_pi_polarCoord_symm hp.2 hq.2 (congrArg Prod.snd h)

theorem mixedRealPolar_image_ae (N : ℕ) : mixedRealPolar '' mixedTarget N =ᵐ[volume] univ := by
  change Prod.map id (Pi.map (fun _ : Fin N ↦ polarCoord.symm)) ''
    (univ ×ˢ univ.pi (fun _ : Fin N ↦ polarCoord.target)) =ᵐ[volume] univ
  rw [Set.prodMap_image_prod, Set.image_id, ← Set.univ_prod_univ, Measure.volume_eq_prod]
  exact Measure.set_prod_ae_eq Filter.EventuallyEq.rfl pi_polarCoord_symm_target_ae_eq_univ

theorem integral_comp_mixedRealPolar {N : ℕ} (f : MixedCart N → ℝ) :
    (∫ p in mixedTarget N, (∏ k : Fin N, (p.2 k).1) * f (mixedRealPolar p)) = ∫ p, f p := by
  rw [← setIntegral_univ (f := f), ← setIntegral_congr_set (mixedRealPolar_image_ae N)]
  have h := (integral_image_eq_integral_abs_det_fderiv_smul volume (measurableSet_mixedTarget N)
    (fun p _ ↦ (hasFDerivAt_mixedRealPolar p).hasFDerivWithinAt) (injOn_mixedRealPolar N) f).symm
  refine (setIntegral_congr_fun (measurableSet_mixedTarget N) ?_).trans h
  intro p hp
  simp only [det_mixedRealDerivative, Finset.abs_prod, smul_eq_mul]
  congr 2
  funext k
  exact (abs_of_pos (hp.2 k trivial).1).symm

def mixedComplexEquiv (N : ℕ) : MixedCart N ≃ᵐ MixedComplex N :=
  (MeasurableEquiv.refl ℝ).prodCongr
    (MeasurableEquiv.piCongrRight (fun _ : Fin N ↦ Complex.measurableEquivRealProd.symm))

theorem volume_preserving_mixedComplexEquiv (N : ℕ) : MeasurePreserving (mixedComplexEquiv N) :=
  (MeasurePreserving.id _).prod
    (volume_preserving_pi (fun _ : Fin N ↦ Complex.volume_preserving_equiv_real_prod.symm))

/-- Actual partial Pi polar change of variables with the angular coordinate untouched. -/
theorem integral_comp_mixedPolar {N : ℕ} (f : MixedComplex N → ℝ) :
    (∫ p in mixedTarget N, (∏ k : Fin N, (p.2 k).1) * f (mixedPolar p)) = ∫ p, f p := by
  rw [← (volume_preserving_mixedComplexEquiv N).integral_comp
    (mixedComplexEquiv N).measurableEmbedding f]
  exact integral_comp_mixedRealPolar (f ∘ mixedComplexEquiv N)

def nativeRegion (N : ℕ) (ε : ℝ) : Set (MixedComplex N) :=
  Icc (-Real.pi) Real.pi ×ˢ univ.pi (fun _ ↦ {z : ℂ | ε ≤ ‖z‖})

def openPolarRegion (N : ℕ) (ε : ℝ) : Set (MixedCart N) :=
  Icc (-Real.pi) Real.pi ×ˢ univ.pi (fun _ ↦ Ici ε ×ˢ Ioo (-Real.pi) Real.pi)

def closedPolarRegion (N : ℕ) (ε : ℝ) : Set (MixedCart N) :=
  Icc (-Real.pi) Real.pi ×ˢ univ.pi (fun _ ↦ Ici ε ×ˢ Icc (-Real.pi) Real.pi)

theorem measurableSet_nativeRegion (N : ℕ) (ε : ℝ) : MeasurableSet (nativeRegion N ε) :=
  measurableSet_Icc.prod (MeasurableSet.univ_pi (fun _ ↦ measurableSet_le measurable_const measurable_norm))

theorem measurableSet_openPolarRegion (N : ℕ) (ε : ℝ) : MeasurableSet (openPolarRegion N ε) :=
  measurableSet_Icc.prod (MeasurableSet.univ_pi (fun _ ↦ measurableSet_Ici.prod measurableSet_Ioo))

theorem openPolarRegion_ae_closed (N : ℕ) (ε : ℝ) :
    openPolarRegion N ε =ᵐ[volume] closedPolarRegion N ε := by
  rw [openPolarRegion, closedPolarRegion, Measure.volume_eq_prod]
  apply Measure.set_prod_ae_eq Filter.EventuallyEq.rfl
  rw [volume_pi]
  apply Measure.ae_eq_set_pi
  intro k hk
  rw [Measure.volume_eq_prod]
  exact Measure.set_prod_ae_eq Filter.EventuallyEq.rfl Ioo_ae_eq_Icc

theorem integral_nativeRegion_eq_closedPolarRegion {N : ℕ} (f : MixedComplex N → ℝ)
    (ε : ℝ) (hε : 0 < ε) :
    (∫ p in nativeRegion N ε, f p) =
      ∫ q in closedPolarRegion N ε, (∏ k : Fin N, (q.2 k).1) * f (mixedPolar q) := by
  rw [← integral_indicator (measurableSet_nativeRegion N ε), ← integral_comp_mixedPolar]
  have hind (p : MixedCart N) (hp : p ∈ mixedTarget N) :
      (∏ k : Fin N, (p.2 k).1) * (nativeRegion N ε).indicator f (mixedPolar p) =
        (openPolarRegion N ε).indicator
          (fun q ↦ (∏ k : Fin N, (q.2 k).1) * f (mixedPolar q)) p := by
    classical
    have hm : mixedPolar p ∈ nativeRegion N ε ↔ p ∈ openPolarRegion N ε := by
      constructor
      · intro hn
        refine ⟨hn.1, fun k hk ↦ ⟨?_, (hp.2 k hk).2⟩⟩
        have hh := hn.2 k hk
        change ε ≤ ‖Complex.polarCoord.symm (p.2 k)‖ at hh
        rwa [Complex.norm_polarCoord_symm, abs_of_pos (hp.2 k hk).1] at hh
      · intro hn
        refine ⟨hn.1, fun k hk ↦ ?_⟩
        change ε ≤ ‖Complex.polarCoord.symm (p.2 k)‖
        rw [Complex.norm_polarCoord_symm, abs_of_pos (hp.2 k hk).1]
        exact (hn.2 k hk).1
    by_cases h : mixedPolar p ∈ nativeRegion N ε
    · rw [indicator_of_mem h, indicator_of_mem (hm.mp h)]
    · rw [indicator_of_notMem h, indicator_of_notMem (mt hm.mpr h), mul_zero]
  calc
    _ = ∫ p in mixedTarget N, (openPolarRegion N ε).indicator
        (fun q ↦ (∏ k : Fin N, (q.2 k).1) * f (mixedPolar q)) p :=
      setIntegral_congr_fun (measurableSet_mixedTarget N) hind
    _ = ∫ p in openPolarRegion N ε, (∏ k : Fin N, (p.2 k).1) * f (mixedPolar p) := by
      rw [setIntegral_indicator (measurableSet_openPolarRegion N ε), inter_eq_right.mpr]
      intro p hp
      refine ⟨trivial, fun k hk ↦ ⟨hε.trans_le (hp.2 k hk).1, (hp.2 k hk).2⟩⟩
    _ = _ := setIntegral_congr_set (openPolarRegion_ae_closed N ε)

theorem mixedMeas_preimage_closedPolarRegion {N : ℕ} (i : Fin (N + 1)) (ε : ℝ) :
    mixedMeas i ⁻¹' closedPolarRegion N ε = NormalCrossingStokes.boundaryRegion i ε := by
  ext x
  have hs := split_fullFace i ε x
  change ((mixedCLM i x).1 ∈ Icc (-Real.pi) Real.pi ∧
      ∀ k ∈ (univ : Set (Fin N)), ((mixedCLM i x).2 k).1 ∈ Ici ε ∧
        ((mixedCLM i x).2 k).2 ∈ Icc (-Real.pi) Real.pi) ↔
    ((∀ k, ε ≤ (split N (faceEmbedding (radiusIndex i) ε x) k).1) ∧
      ∀ k, (split N (faceEmbedding (radiusIndex i) ε x) k).2 ∈ Icc (-Real.pi) Real.pi)
  rw [hs]
  simp only [Fin.forall_iff_succAbove i, Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove,
    le_refl, true_and, mem_univ, forall_const, mem_Ici]
  constructor
  · rintro ⟨ht, ho⟩
    exact ⟨fun k ↦ (ho k).1, ht, fun k ↦ (ho k).2⟩
  · rintro ⟨hr, ht, ho⟩
    exact ⟨ht, fun k ↦ ⟨hr k, ho k⟩⟩

/-- The exact boundary-coordinate bridge. The same inherited column order is used
on both sides, so the only factor introduced is the proved remaining polar Jacobian. -/
theorem boundaryIntegral_eq_native {N : ℕ} (ω : CrossingForm N) (i : Fin (N + 1))
    (ε : ℝ) (hε : 0 < ε) :
    NormalCrossingStokes.boundaryIntegral ω i ε =
      ∫ p in nativeRegion N ε, nativeDensity ω i ε p := by
  have h := (volume_preserving_mixedMeas i).setIntegral_preimage_emb (mixedMeas i).measurableEmbedding
    (fun q : MixedCart N ↦ (∏ k : Fin N, (q.2 k).1) * nativeDensity ω i ε (mixedPolar q))
    (closedPolarRegion N ε)
  rw [mixedMeas_preimage_closedPolarRegion] at h
  have heq (x : Coord (Degree N)) : mixedMeas i x = mixedEquiv i x := rfl
  simp only [heq] at h
  simp_rw [← cylinderDensity_eq_jacobian] at h
  exact h.trans (integral_nativeRegion_eq_closedPolarRegion (nativeDensity ω i ε) ε hε).symm

/-- The normal-crossing theorem can now consume limits of literal circle × complex
remaining-coordinate integrals, with no supplied boundary-coordinate identity. -/
theorem integral_extDeriv_eq_zero_of_native_limits {N : ℕ} (ω : CrossingForm N)
    (hω : ContDiffOn ℝ 1 ω (regularLocus N)) (hcompact : HasCompactSupport ω)
    (hL1 : Integrable (fun z ↦ extDeriv ω z (frame N)))
    (hboundary : ∀ i : Fin (N + 1),
      Tendsto (fun ε ↦ ∫ p in nativeRegion N ε, nativeDensity ω i ε p) (𝓝[>] 0) (𝓝 0)) :
    (∫ z : Space N, extDeriv ω z (frame N)) = 0 := by
  apply NormalCrossingStokes.integral_extDeriv_frame_eq_zero ω hω hcompact hL1
  intro i
  apply (hboundary i).congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (boundaryIntegral_eq_native ω i ε hε).symm

def angularSlot {N : ℕ} (i : Fin (N + 1)) : Fin (Degree N) := ⟨N + i.val, by dsimp [Degree]; omega⟩

@[simp] theorem angularSlot_val {N : ℕ} (i : Fin (N + 1)) : (angularSlot i).val = N + i.val := rfl

@[simp] theorem succAbove_angularSlot {N : ℕ} (i : Fin (N + 1)) :
    (radiusIndex i).succAbove (angularSlot i) = angleIndex i := by
  rw [Fin.succAbove_of_le_castSucc _ _ (by
    change i.val ≤ N + i.val
    omega)]
  apply Fin.ext
  change N + i.val + 1 = N + 1 + i.val
  omega

@[simp] theorem faceTangent_single {n : ℕ} (i : Fin (n + 1)) (j : Fin n) :
    faceTangent i (Pi.single j 1) = Pi.single (i.succAbove j) 1 :=
  faceTangent_standardBasis i j

theorem mixedFrame_fst {N : ℕ} (i : Fin (N + 1)) (j : Fin (Degree N)) :
    (mixedFrame i j).1 = if j = angularSlot i then 1 else 0 := by
  have heq : angleIndex i = (radiusIndex i).succAbove j ↔ j = angularSlot i := by
    rw [← succAbove_angularSlot]
    exact ⟨fun h ↦ ((radiusIndex i).succAbove_right_injective h).symm,
      fun h ↦ congrArg (radiusIndex i).succAbove h.symm⟩
  simp [mixedFrame, mixedEquiv_apply, mixedConvert, mixedCLM,
    faceTangent_single, split, standardBasis, Pi.single_apply, heq]

theorem mixedFrame_angularSlot {N : ℕ} (i : Fin (N + 1)) :
    mixedFrame i (angularSlot i) = (1, 0) := by
  apply Prod.ext
  · simp [mixedFrame_fst]
  · funext k
    simp [mixedFrame, mixedEquiv_apply, mixedConvert, mixedCLM, otherConvert,
      faceTangent_single, split, standardBasis, Pi.single_apply,
      Complex.equivRealProdCLM_symm_apply]

def tangentFrame {N : ℕ} (i : Fin (N + 1)) (r : ℝ) (p : MixedComplex N) :
    Fin (Degree N) → Space N := (nativeDerivative i r p : MixedComplex N → Space N) ∘ mixedFrame i

theorem nativeDensity_eq_tangentFrame {N : ℕ} (ω : CrossingForm N) (i : Fin (N + 1))
    (r : ℝ) (p : MixedComplex N) : nativeDensity ω i r p = ω (nativeCylinder i r p) (tangentFrame i r p) := by
  rw [nativeDensity, (hasFDerivAt_nativeCylinder i r p).fderiv]
  rfl

theorem tangentFrame_distinguished {N : ℕ} (i : Fin (N + 1)) (r : ℝ) (p : MixedComplex N)
    (j : Fin (Degree N)) (hj : j ≠ angularSlot i) : tangentFrame i r p j i = 0 := by
  simp [tangentFrame, nativeDerivative, mixedFrame_fst, hj]

theorem tangentFrame_angularSlot {N : ℕ} (i : Fin (N + 1)) (r : ℝ) (p : MixedComplex N) :
    tangentFrame i r p (angularSlot i) = r • LogMonomial.unitAngularTangent i p.1 := by
  funext k
  induction k using i.succAboveCases with
  | x =>
    simp [tangentFrame, mixedFrame_angularSlot, nativeDerivative, LogMonomial.unitAngularTangent,
      LogCircle.shrinkingCircleTangent_apply, LogCircle.shrinkingCircle, Complex.real_smul]
    ring
  | p k =>
    simp [tangentFrame, mixedFrame_angularSlot, nativeDerivative, LogMonomial.unitAngularTangent]

/-- Moving the distinguished angular column first is the explicit prefix-cycle permutation. -/
def angleFirstFrame {N : ℕ} (i : Fin (N + 1)) (r : ℝ) (p : MixedComplex N) :
    Fin (Degree N) → Space N := tangentFrame i r p ∘ (angularSlot i).cycleRange.symm

/-- The exact orientation factor of the angle-first convention is (-1)^(N+i). -/
theorem angleFirstFrame_sign {N : ℕ} (α : Space N [⋀^Fin (Degree N)]→L[ℝ] ℝ)
    (i : Fin (N + 1)) (r : ℝ) (p : MixedComplex N) :
    α (angleFirstFrame i r p) = (-1 : ℝ) ^ (N + i.val) * α (tangentFrame i r p) := by
  change α.toAlternatingMap (angleFirstFrame i r p) =
    (-1 : ℝ) ^ (N + i.val) * α.toAlternatingMap (tangentFrame i r p)
  have h := α.toAlternatingMap.map_perm (tangentFrame i r p) (angularSlot i).cycleRange.symm
  simpa only [angleFirstFrame, Equiv.Perm.sign_symm, Fin.sign_cycleRange, angularSlot_val,
    Units.smul_def, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one, zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one] using h

def optionCoordinates {N : ℕ} (i : Fin (N + 1)) : Space N ≃L[ℝ] (Option (Fin N) → ℂ) :=
  ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Option (Fin N) ↦ ℂ) (finSuccEquiv' i)

theorem optionCoordinates_nativeCylinder {N : ℕ} (i : Fin (N + 1)) (r : ℝ) (p : MixedComplex N) :
    optionCoordinates i (nativeCylinder i r p) = LogMonomial.circleFacePoint r p := by
  funext ν
  cases ν <;> simp [optionCoordinates, ContinuousLinearEquiv.piCongrLeft,
    Equiv.piCongrLeft_apply, nativeCylinder, LogMonomial.circleFacePoint, LogCircle.shrinkingCircle]

def optionFrame {N : ℕ} (i : Fin (N + 1)) (r : ℝ) (p : MixedComplex N) :
    Fin (Degree N) → Option (Fin N) → ℂ := optionCoordinates i ∘ tangentFrame i r p

theorem optionFrame_angularSlot {N : ℕ} (i : Fin (N + 1)) (r : ℝ) (p : MixedComplex N) :
    optionFrame i r p (angularSlot i) = r • LogMonomial.unitAngularTangent none p.1 := by
  rw [optionFrame, Function.comp_apply, tangentFrame_angularSlot, map_smul]
  congr 1
  funext ν
  cases ν <;> simp [optionCoordinates, ContinuousLinearEquiv.piCongrLeft,
    Equiv.piCongrLeft_apply, LogMonomial.unitAngularTangent]

theorem optionFrame_other_none {N : ℕ} (i : Fin (N + 1)) (r : ℝ) (p : MixedComplex N)
    (j : Fin (Degree N)) (hj : j ≠ angularSlot i) : optionFrame i r p j none = 0 := by
  simpa [optionFrame, optionCoordinates, ContinuousLinearEquiv.piCongrLeft,
    Equiv.piCongrLeft_apply] using tangentFrame_distinguished i r p j hj

theorem periodic_nativeDensity {N : ℕ} (ω : CrossingForm N) (i : Fin (N + 1))
    (r : ℝ) (z : Fin N → ℂ) :
    Function.Periodic (fun θ ↦ nativeDensity ω i r (θ, z)) (2 * Real.pi) := by
  intro θ
  simp only [nativeDensity, (hasFDerivAt_nativeCylinder i r _).fderiv, nativeCylinder,
    nativeDerivative, LogCircle.shrinkingCircleTangent, LogCircle.shrinkingCircle,
    PuncturedCoordinateStokes.periodic_circleParameter θ]

def positiveNativeRegion (N : ℕ) (ε : ℝ) : Set (MixedComplex N) :=
  Icc (0 : ℝ) (2 * Real.pi) ×ˢ univ.pi (fun _ ↦ {z : ℂ | ε ≤ ‖z‖})

/-- Periodic transfer to the literal [0,2π] interval used by the monomial bounds.
Both integrability premises concern actual coefficients and actual product measures. -/
theorem integral_nativeRegion_eq_positive {N : ℕ} (ω : CrossingForm N) (i : Fin (N + 1))
    (ε : ℝ)
    (hcenter : IntegrableOn (nativeDensity ω i ε) (nativeRegion N ε))
    (hpositive : IntegrableOn (nativeDensity ω i ε) (positiveNativeRegion N ε)) :
    (∫ p in nativeRegion N ε, nativeDensity ω i ε p) =
      ∫ p in positiveNativeRegion N ε, nativeDensity ω i ε p := by
  rw [nativeRegion, PuncturedProductStokes.setIntegral_prod_symm _ _ _ hcenter,
    positiveNativeRegion, PuncturedProductStokes.setIntegral_prod_symm _ _ _ hpositive]
  apply setIntegral_congr_fun (MeasurableSet.univ_pi (fun _ ↦ measurableSet_le measurable_const measurable_norm))
  intro z hz
  have h := (periodic_nativeDensity ω i ε z).intervalIntegral_add_eq 0 (-Real.pi)
  have hπ : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  have h2π : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  simpa only [zero_add, show -Real.pi + 2 * Real.pi = Real.pi by ring,
    intervalIntegral.integral_of_le hπ, intervalIntegral.integral_of_le h2π,
    setIntegral_congr_set (Ioc_ae_eq_Icc (α := ℝ) (μ := volume))] using h.symm

theorem boundaryIntegral_eq_native_positive {N : ℕ} (ω : CrossingForm N) (i : Fin (N + 1))
    (ε : ℝ) (hε : 0 < ε)
    (hcenter : IntegrableOn (nativeDensity ω i ε) (nativeRegion N ε))
    (hpositive : IntegrableOn (nativeDensity ω i ε) (positiveNativeRegion N ε)) :
    NormalCrossingStokes.boundaryIntegral ω i ε =
      ∫ p in positiveNativeRegion N ε, nativeDensity ω i ε p :=
  (boundaryIntegral_eq_native ω i ε hε).trans
    (integral_nativeRegion_eq_positive ω i ε hcenter hpositive)

def optionLift {N : ℕ} (i : Fin (N + 1))
    (β : (Option (Fin N) → ℂ) → (Option (Fin N) → ℂ) [⋀^Fin (Degree N)]→L[ℝ] ℝ) : CrossingForm N :=
  fun z ↦ (β (optionCoordinates i z)).compContinuousLinearMap (optionCoordinates i).toContinuousLinearMap

theorem nativeDensity_optionLift {N : ℕ} (i : Fin (N + 1))
    (β : (Option (Fin N) → ℂ) → (Option (Fin N) → ℂ) [⋀^Fin (Degree N)]→L[ℝ] ℝ)
    (r : ℝ) (p : MixedComplex N) :
    nativeDensity (optionLift i β) i r p = β (LogMonomial.circleFacePoint r p) (optionFrame i r p) := by
  rw [nativeDensity_eq_tangentFrame, optionLift, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    optionCoordinates_nativeCylinder]
  rfl

/-- An actual compact cutoff multiplying the actual logarithmic monomial primitive. -/
def cutoffPrimitive {N : ℕ} (i : Fin (N + 1))
    (a : Fin (Dim N) → Option (Fin N) → ℤ)
    (u : Fin (Dim N) → (Option (Fin N) → ℂ) → ℂ) (χ : Space N → ℝ) : CrossingForm N :=
  χ • optionLift i (LogRadialPrimitive.primitive (LogMonomial.coordinateMonomial a u))

theorem hasCompactSupport_cutoffPrimitive {N : ℕ} (i : Fin (N + 1))
    (a : Fin (Dim N) → Option (Fin N) → ℤ)
    (u : Fin (Dim N) → (Option (Fin N) → ℂ) → ℂ) (χ : Space N → ℝ)
    (hχ : HasCompactSupport χ) : HasCompactSupport (cutoffPrimitive i a u χ) :=
  hχ.smul_right

theorem nativeDensity_cutoffPrimitive {N : ℕ} (i : Fin (N + 1))
    (a : Fin (Dim N) → Option (Fin N) → ℤ)
    (u : Fin (Dim N) → (Option (Fin N) → ℂ) → ℂ) (χ : Space N → ℝ)
    (r : ℝ) (p : MixedComplex N) :
    nativeDensity (cutoffPrimitive i a u χ) i r p =
      χ (nativeCylinder i r p) * LogMonomial.circleFacePrimitive a u (optionFrame i) r p := by
  rw [nativeDensity_eq_tangentFrame]
  change (χ (nativeCylinder i r p) • optionLift i
    (LogRadialPrimitive.primitive (LogMonomial.coordinateMonomial a u)) (nativeCylinder i r p))
      (tangentFrame i r p) = _
  rw [ContinuousAlternatingMap.smul_apply, smul_eq_mul, ← nativeDensity_eq_tangentFrame,
    nativeDensity_optionLift]
  rfl

/-- The actual compactly cut off monomial primitive feeds the exact cylinder bridge. -/
theorem boundaryIntegral_cutoffPrimitive_eq {N : ℕ} (i : Fin (N + 1))
    (a : Fin (Dim N) → Option (Fin N) → ℤ)
    (u : Fin (Dim N) → (Option (Fin N) → ℂ) → ℂ) (χ : Space N → ℝ)
    (ε : ℝ) (hε : 0 < ε) :
    NormalCrossingStokes.boundaryIntegral (cutoffPrimitive i a u χ) i ε =
      ∫ p in nativeRegion N ε,
        χ (nativeCylinder i ε p) * LogMonomial.circleFacePrimitive a u (optionFrame i) ε p := by
  rw [boundaryIntegral_eq_native _ i ε hε]
  simp_rw [nativeDensity_cutoffPrimitive]

theorem angleFirstFrame_zero {N : ℕ} (i : Fin (N + 1)) (r : ℝ) (p : MixedComplex N) :
    angleFirstFrame i r p 0 = r • LogMonomial.unitAngularTangent i p.1 := by
  rw [angleFirstFrame, Function.comp_apply, Fin.cycleRange_symm_zero, tangentFrame_angularSlot]

theorem mixedFrame_snd {N : ℕ} (i : Fin (N + 1)) (j : Fin (Degree N)) (k : Fin N) :
    (mixedFrame i j).2 k =
      (if radiusIndex (i.succAbove k) = (radiusIndex i).succAbove j then (1 : ℂ) else 0) +
      (if angleIndex (i.succAbove k) = (radiusIndex i).succAbove j then Complex.I else 0) := by
  simp [mixedFrame, mixedEquiv_apply, mixedConvert, mixedCLM, otherConvert,
    faceTangent_single, split, standardBasis, Pi.single_apply, Complex.equivRealProdCLM_symm_apply]
  split_ifs <;> simp

theorem norm_mixedFrame_snd_le_one {N : ℕ} (i : Fin (N + 1)) (j : Fin (Degree N)) (k : Fin N) :
    ‖(mixedFrame i j).2 k‖ ≤ 1 := by
  rw [mixedFrame_snd]
  by_cases hr : radiusIndex (i.succAbove k) = (radiusIndex i).succAbove j
  · have ha : angleIndex (i.succAbove k) ≠ (radiusIndex i).succAbove j := by
      rw [← hr]
      exact angleIndex_ne_radiusIndex _ _
    simp [hr, ha]
  · by_cases ha : angleIndex (i.succAbove k) = (radiusIndex i).succAbove j <;> simp [hr, ha]

/-- The actual inherited tangent frame is uniformly bounded for shrinking radii at most one. -/
theorem norm_tangentFrame_le_one {N : ℕ} (i : Fin (N + 1)) (r : ℝ)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (p : MixedComplex N) (j : Fin (Degree N)) :
    ‖tangentFrame i r p j‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro k
  induction k using i.succAboveCases with
  | x =>
    by_cases hj : j = angularSlot i
    · subst j
      simp only [tangentFrame, Function.comp_apply, nativeDerivative, ContinuousLinearMap.pi_apply,
        Fin.insertNth_apply_same, ContinuousLinearMap.comp_apply, mixedFrame_angularSlot]
      change ‖LogCircle.shrinkingCircleTangent r p.1 1‖ ≤ 1
      simpa only [LogCircle.norm_shrinkingCircleTangent_one, abs_of_nonneg hr] using hr1
    · rw [tangentFrame_distinguished i r p j hj, norm_zero]
      exact zero_le_one
  | p k =>
    change ‖(nativeDerivative i r p (mixedFrame i j)) (i.succAbove k)‖ ≤ 1
    simp only [nativeDerivative, ContinuousLinearMap.pi_apply, Fin.insertNth_apply_succAbove,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]
    exact norm_mixedFrame_snd_le_one i j k

theorem norm_optionFrame_le_one {N : ℕ} (i : Fin (N + 1)) (r : ℝ)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (p : MixedComplex N) (j : Fin (Degree N)) :
    ‖optionFrame i r p j‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro ν
  have h := (norm_le_pi_norm (tangentFrame i r p j) ((finSuccEquiv' i).symm ν)).trans
    (norm_tangentFrame_le_one i r hr hr1 p j)
  simpa [optionFrame, optionCoordinates, ContinuousLinearEquiv.piCongrLeft,
    Equiv.piCongrLeft_apply] using h

/-- The proved concrete cylinder frame discharges every tangent hypothesis in
the existing monomial flux estimate. Only actual unit/measurability bounds remain. -/
theorem primitive_flux_spec_actualFrame {N : ℕ} (i : Fin (N + 1))
    (a : Fin (Dim N) → Option (Fin N) → ℤ)
    (u : Fin (Dim N) → (Option (Fin N) → ℂ) → ℂ)
    (δ : Fin N → ℝ) (D c L r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) (hc : 0 < c)
    (hF : AEStronglyMeasurable (LogMonomial.circleFacePrimitive a u (optionFrame i) r)
      (volume.restrict (NormalCrossing.boundaryRegion δ)))
    (hu : ∀ p ∈ NormalCrossing.boundaryRegion δ, ∀ j,
      DifferentiableAt ℝ (u j) (LogMonomial.circleFacePoint r p))
    (hunit : ∀ p ∈ NormalCrossing.boundaryRegion δ, ∀ j,
      c ≤ ‖u j (LogMonomial.circleFacePoint r p)‖)
    (hD : ∀ p ∈ NormalCrossing.boundaryRegion δ, ∀ j : Fin (Degree N),
      ‖fderiv ℝ (u j.succ) (LogMonomial.circleFacePoint r p)‖ ≤ D)
    (hL : ∀ p ∈ NormalCrossing.boundaryRegion δ,
      |Real.log ‖u 0 (LogMonomial.circleFacePoint r p)‖| ≤ L) :
    IntegrableOn (LogMonomial.circleFacePrimitive a u (optionFrame i) r) (NormalCrossing.boundaryRegion δ) ∧
      ‖∫ p in NormalCrossing.boundaryRegion δ, LogMonomial.circleFacePrimitive a u (optionFrame i) r p‖ ≤
        LogMonomial.primitiveFluxBound δ
          (LogMonomial.uniformDeterminantBound (fun j : Fin (Degree N) ↦ a j.succ) D c)
          (LogMonomial.logarithmBound (a 0) L) r := by
  apply LogMonomial.circleFacePrimitive_flux_spec_of_unitBounds a u (optionFrame i) (angularSlot i)
    δ D c L r hr hc hF hu hunit hD
  · exact fun p hp j ↦ norm_optionFrame_le_one i r hr.le hr1 p j
  · exact fun p hp ↦ optionFrame_angularSlot i r p
  · exact fun p hp j hj ↦ optionFrame_other_none i r p j hj
  · exact hL

/-- A bounded actual cutoff and actual unit bounds control the concrete native
cylinder density of the actual compactly cut off primitive. -/
theorem norm_nativeDensity_cutoffPrimitive_le {N : ℕ} (i : Fin (N + 1))
    (a : Fin (Dim N) → Option (Fin N) → ℤ)
    (u : Fin (Dim N) → (Option (Fin N) → ℂ) → ℂ) (χ : Space N → ℝ)
    (δ : Fin N → ℝ) (D c L r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) (hc : 0 < c)
    (p : MixedComplex N) (hp : p ∈ NormalCrossing.boundaryRegion δ)
    (hχ : ‖χ (nativeCylinder i r p)‖ ≤ 1)
    (hu : ∀ j, DifferentiableAt ℝ (u j) (LogMonomial.circleFacePoint r p))
    (hunit : ∀ j, c ≤ ‖u j (LogMonomial.circleFacePoint r p)‖)
    (hD : ∀ j : Fin (Degree N), ‖fderiv ℝ (u j.succ) (LogMonomial.circleFacePoint r p)‖ ≤ D)
    (hL : |Real.log ‖u 0 (LogMonomial.circleFacePoint r p)‖| ≤ L) :
    ‖nativeDensity (cutoffPrimitive i a u χ) i r p‖ ≤
      LogMonomial.uniformDeterminantBound (fun j : Fin (Degree N) ↦ a j.succ) D c *
        LogMonomial.logarithmBound (a 0) L * r * (1 + |Real.log r|) *
          NormalCrossing.boundaryMajorant (fun _ : Fin N ↦ 1) p := by
  have hcoeff := LogMonomial.boundaryCoefficient_le_unitBounds
    (fun j : Fin (Degree N) ↦ a j.succ) (fun j ↦ u j.succ) (optionFrame i r p)
    (LogMonomial.circleFacePoint r p) (angularSlot i) p.1 D c hc hD
    (fun j ↦ hunit j.succ) (fun j ↦ norm_optionFrame_le_one i r hr.le hr1 p j)
  have hC : 0 ≤ LogMonomial.uniformDeterminantBound (fun j : Fin (Degree N) ↦ a j.succ) D c := by
    unfold LogMonomial.uniformDeterminantBound LogMonomial.exponentBound
    positivity
  have h := LogMonomial.norm_primitive_circleFace_le a u (optionFrame i r p) (angularSlot i) r hr
    p δ hp hu (fun j ↦ norm_pos_iff.mp (hc.trans_le (hunit j)))
    (optionFrame_angularSlot i r p) (fun j hj ↦ optionFrame_other_none i r p j hj)
    _ L hC hcoeff hL
  rw [nativeDensity_cutoffPrimitive, norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) hχ).trans h

/-- Arbitrary additional measurable remaining-normal cutoffs preserve the actual
compact-cutoff primitive flux bound. -/
theorem cutoffFlux_spec_actualPrimitive {N : ℕ} (i : Fin (N + 1))
    (a : Fin (Dim N) → Option (Fin N) → ℤ)
    (u : Fin (Dim N) → (Option (Fin N) → ℂ) → ℂ) (χ : Space N → ℝ)
    (δ : Fin N → ℝ) (D c L r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) (hc : 0 < c)
    (S : Set (MixedComplex N)) (hS : MeasurableSet S) (hsub : S ⊆ NormalCrossing.boundaryRegion δ)
    (hF : AEStronglyMeasurable (nativeDensity (cutoffPrimitive i a u χ) i r)
      (volume.restrict (NormalCrossing.boundaryRegion δ)))
    (hχ : ∀ p ∈ NormalCrossing.boundaryRegion δ, ‖χ (nativeCylinder i r p)‖ ≤ 1)
    (hu : ∀ p ∈ NormalCrossing.boundaryRegion δ, ∀ j,
      DifferentiableAt ℝ (u j) (LogMonomial.circleFacePoint r p))
    (hunit : ∀ p ∈ NormalCrossing.boundaryRegion δ, ∀ j,
      c ≤ ‖u j (LogMonomial.circleFacePoint r p)‖)
    (hD : ∀ p ∈ NormalCrossing.boundaryRegion δ, ∀ j : Fin (Degree N),
      ‖fderiv ℝ (u j.succ) (LogMonomial.circleFacePoint r p)‖ ≤ D)
    (hL : ∀ p ∈ NormalCrossing.boundaryRegion δ,
      |Real.log ‖u 0 (LogMonomial.circleFacePoint r p)‖| ≤ L) :
    IntegrableOn (nativeDensity (cutoffPrimitive i a u χ) i r) S ∧
      ‖∫ p in S, nativeDensity (cutoffPrimitive i a u χ) i r p‖ ≤
        LogMonomial.primitiveFluxBound δ
          (LogMonomial.uniformDeterminantBound (fun j : Fin (Degree N) ↦ a j.succ) D c)
          (LogMonomial.logarithmBound (a 0) L) r := by
  let C := LogMonomial.uniformDeterminantBound (fun j : Fin (Degree N) ↦ a j.succ) D c
  let K := LogMonomial.logarithmBound (a 0) L
  have h := NormalCrossing.cutoffSetFlux_spec (fun _ : Fin N ↦ 1) δ 0
    (C * K * (1 + |Real.log r|)) r S hS hsub (nativeDensity (cutoffPrimitive i a u χ) i r) hF
    ?_
  · refine ⟨h.1, h.2.trans_eq ?_⟩
    simp only [NormalCrossing.fluxBound, LogMonomial.primitiveFluxBound, pow_zero]
    ring
  · filter_upwards [ae_restrict_mem (NormalCrossing.measurableSet_boundaryRegion δ)] with p hp
    have hb := norm_nativeDensity_cutoffPrimitive_le i a u χ δ D c L r hr hr1 hc p hp
      (hχ p hp) (hu p hp) (hunit p hp) (hD p hp) (hL p hp)
    refine hb.trans_eq ?_
    simp only [NormalCrossing.boundaryMajorant, pow_zero]
    dsimp [C, K]
    ring

/-- The actual monomial cutoff primitive flux tends to zero uniformly under
arbitrary measurable remaining-normal cutoff families. -/
theorem tendsto_cutoffFlux_actualPrimitive {N : ℕ} (i : Fin (N + 1))
    (a : Fin (Dim N) → Option (Fin N) → ℤ)
    (u : Fin (Dim N) → (Option (Fin N) → ℂ) → ℂ) (χ : Space N → ℝ)
    (δ : Fin N → ℝ) (D c L R : ℝ) (hR : 0 < R) (hR1 : R ≤ 1) (hc : 0 < c)
    (S : ℝ → Set (MixedComplex N))
    (hS : ∀ r ∈ Ioo 0 R, MeasurableSet (S r))
    (hsub : ∀ r ∈ Ioo 0 R, S r ⊆ NormalCrossing.boundaryRegion δ)
    (hF : ∀ r ∈ Ioo 0 R, AEStronglyMeasurable (nativeDensity (cutoffPrimitive i a u χ) i r)
      (volume.restrict (NormalCrossing.boundaryRegion δ)))
    (hχ : ∀ r ∈ Ioo 0 R, ∀ p ∈ NormalCrossing.boundaryRegion δ, ‖χ (nativeCylinder i r p)‖ ≤ 1)
    (hu : ∀ r ∈ Ioo 0 R, ∀ p ∈ NormalCrossing.boundaryRegion δ, ∀ j,
      DifferentiableAt ℝ (u j) (LogMonomial.circleFacePoint r p))
    (hunit : ∀ r ∈ Ioo 0 R, ∀ p ∈ NormalCrossing.boundaryRegion δ, ∀ j,
      c ≤ ‖u j (LogMonomial.circleFacePoint r p)‖)
    (hD : ∀ r ∈ Ioo 0 R, ∀ p ∈ NormalCrossing.boundaryRegion δ, ∀ j : Fin (Degree N),
      ‖fderiv ℝ (u j.succ) (LogMonomial.circleFacePoint r p)‖ ≤ D)
    (hL : ∀ r ∈ Ioo 0 R, ∀ p ∈ NormalCrossing.boundaryRegion δ,
      |Real.log ‖u 0 (LogMonomial.circleFacePoint r p)‖| ≤ L) :
    Tendsto (fun r ↦ ∫ p in S r, nativeDensity (cutoffPrimitive i a u χ) i r p) (𝓝[>] 0) (𝓝 0) := by
  apply squeeze_zero_norm' _
    (LogMonomial.tendsto_primitiveFluxBound δ
      (LogMonomial.uniformDeterminantBound (fun j : Fin (Degree N) ↦ a j.succ) D c)
      (LogMonomial.logarithmBound (a 0) L))
  filter_upwards [Ioo_mem_nhdsGT hR] with r hr
  exact (cutoffFlux_spec_actualPrimitive i a u χ δ D c L r hr.1 (hr.2.le.trans hR1) hc
    (S r) (hS r hr) (hsub r hr) (hF r hr) (hχ r hr) (hu r hr) (hunit r hr)
    (hD r hr) (hL r hr)).2

end EnvelopingIsomorphism.Deformation.Kontsevich.NormalCrossingCylinderCoordinates
