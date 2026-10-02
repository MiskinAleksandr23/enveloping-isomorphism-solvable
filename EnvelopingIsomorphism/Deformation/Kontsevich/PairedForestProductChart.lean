import EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestProductOverlap
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

/-! Genuine local diffeomorphisms between actual strict paired forest faces and
coarse/planar product coordinates, with the explicit DR inverse. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestProductChart
open Configuration PairedForestSimpleCluster PairedForestSmoothProduct PairedForestProductOverlap
open InteriorGraphFaceCoordinates ForestRadialFaceClassification BoxStokes
open scoped Classical Topology
variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r + 1)
  (x : Compactification (0 : Fin (n + 1)) m) (o : ForestRadialFaceClassification.Orbit 0 x)
  (ho : kind 0 x o = .paired)

include hdim in
theorem finrank_product : Module.finrank ℝ (Product x o ho) = r := by
  have h := ClusterAngularCoordinates.finrank_eq (m := m)
    (anchor_mem x o ho) (reference_mem x o ho) (reference_ne_anchor x o ho) (anchor_global x o ho)
  simp only [ClusterAngularCoordinates, Module.finrank_prod, Module.finrank_pi_fintype,
    Complex.finrank_real_complex, Module.finrank_self, Finset.sum_const, Finset.card_univ,
    smul_eq_mul, Fintype.card_fin, mul_one] at h
  simp only [Product, ProductCoordinates, ShapeCoordinates, CoarseCoordinates,
    InteriorFiberAngleSplit.Parameters, InteriorFiberAngleSplit.Shape, GraphForms.Coordinates,
    Module.finrank_prod, Module.finrank_pi_fintype, Complex.finrank_real_complex,
    Module.finrank_self, Finset.sum_const, Finset.card_univ, smul_eq_mul, Fintype.card_fin, mul_one]
  dsimp [GraphForms.dimension] at hdim
  dsimp [shapeN, coarseN]
  omega

variable (z : Source hdim x o)

def map : Coord r → Product x o ho := toProduct hdim x o ho (phase hdim x o ho z)

theorem differential_leftInverse :
    (fderiv ℝ (PairedForestProductOverlap.inverse hdim x o ho) (map hdim x o ho z z.val)).comp
      (fderiv ℝ (map hdim x o ho z) z.val) = ContinuousLinearMap.id ℝ (Coord r) := by
  have hd := ((contDiffAt_inverse hdim x o ho (phase hdim x o ho z) z).differentiableAt (by simp)).hasFDerivAt.comp z.val
    ((contDiffAt_toProduct hdim x o ho z).differentiableAt (by simp)).hasFDerivAt
  have he : (PairedForestProductOverlap.inverse hdim x o ho ∘ map hdim x o ho z) =ᶠ[𝓝 z.val] id :=
    Filter.eventuallyEq_of_mem ((ForestRadialFaceImmersion.isOpen_source hdim x o).mem_nhds z.property)
      (fun w hw ↦ inverse_toProduct hdim x o ho (phase hdim x o ho z) ⟨w, hw⟩)
  have h := hd.fderiv
  dsimp only [map] at he ⊢
  rw [he.fderiv_eq, fderiv_id] at h
  exact h.symm

theorem differential_bijective : Function.Bijective (fderiv ℝ (map hdim x o ho z) z.val) := by
  have hi : Function.LeftInverse
      (fderiv ℝ (PairedForestProductOverlap.inverse hdim x o ho) (map hdim x o ho z z.val))
      (fderiv ℝ (map hdim x o ho z) z.val) := fun v ↦
    congrArg (fun L : Coord r →L[ℝ] Coord r ↦ L v) (differential_leftInverse hdim x o ho z)
  have hdim' : Module.finrank ℝ (Coord r) = Module.finrank ℝ (Product x o ho) := by
    rw [finrank_product hdim]
    simp [Coord]
  exact ⟨hi.injective, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim').mp hi.injective⟩

def differential : Coord r ≃L[ℝ] Product x o ho :=
  ContinuousLinearEquiv.ofBijective (fderiv ℝ (map hdim x o ho z) z.val)
    (LinearMap.ker_eq_bot.mpr (differential_bijective hdim x o ho z).1)
    (LinearMap.range_eq_top.mpr (differential_bijective hdim x o ho z).2)

theorem hasStrictFDerivAt_map : HasStrictFDerivAt (map hdim x o ho z)
    (differential hdim x o ho z : Coord r →L[ℝ] Product x o ho) z.val := by
  change HasStrictFDerivAt (map hdim x o ho z) (fderiv ℝ (map hdim x o ho z) z.val) z.val
  exact (contDiffAt_toProduct hdim x o ho z).hasStrictFDerivAt (by simp)

def smoothSource : Set (Coord r) := Source hdim x o ∩ {w |
  ((phase hdim x o ho z : ℂ)⁻¹ * rawVelocity hdim x o ho (reference x o ho)
    (faceEmbedding (axis hdim x o) 0 w)) ∈ Complex.slitPlane}

theorem isOpen_smoothSource : IsOpen (smoothSource hdim x o ho z) := by
  apply isOpen_iff_mem_nhds.mpr
  intro w hw
  apply Filter.inter_mem ((ForestRadialFaceImmersion.isOpen_source hdim x o).mem_nhds hw.1)
  have hv : ContinuousAt (rawVelocity hdim x o ho (reference x o ho))
      (faceTangent (axis hdim x o) w) :=
    (contDiffAt_rawVelocity hdim x o ho ⟨w, hw.1⟩ (reference x o ho)).continuousAt
  have hc : ContinuousAt (fun q : Coord r ↦ rawVelocity hdim x o ho (reference x o ho)
      (faceTangent (axis hdim x o) q)) w :=
    hv.comp (faceTangent (axis hdim x o)).continuous.continuousAt
  exact (continuousAt_const.mul hc).preimage_mem_nhds (Complex.isOpen_slitPlane.mem_nhds hw.2)

theorem self_mem_smoothSource : z.val ∈ smoothSource hdim x o ho z := by
  refine ⟨z.property, ?_⟩
  change ((phase hdim x o ho z : ℂ)⁻¹ * (phase hdim x o ho z : ℂ)) ∈ Complex.slitPlane
  simp [(phase hdim x o ho z).coe_ne_zero]

theorem contDiffAt_map {w : Coord r} (hw : w ∈ smoothSource hdim x o ho z) :
    ContDiffAt ℝ ⊤ (map hdim x o ho z) w := by
  let q : Source hdim x o := ⟨w, hw.1⟩
  have ha : ContDiffAt ℝ ⊤ (angle hdim x o ho (phase hdim x o ho z)) (facePoint hdim x o q) := by
    apply ContDiffAt.add contDiffAt_const
    exact (ForestShapeProjectionSmooth.contDiffAt_angleInverseRaw _ _ hw.2).comp _
      (contDiffAt_rawVelocity hdim x o ho q (reference x o ho))
  have hf : ContDiffAt ℝ ⊤ (fullToProduct hdim x o ho (phase hdim x o ho z)) (facePoint hdim x o q) := by
    apply ContDiffAt.prodMk
    · apply ContDiffAt.prodMk ha
      apply contDiffAt_pi.mpr
      intro j
      simpa only [div_eq_mul_inv, Pi.inv_apply] using
        (contDiffAt_rawVelocity hdim x o ho q (shapeEnum.symm j).val).mul
          ((contDiffAt_rawVelocity hdim x o ho q (reference x o ho)).inv (phase hdim x o ho q).coe_ne_zero)
    · exact (contDiffAt_pi.mpr fun j ↦ contDiffAt_rawBase hdim x o ho q (coarseEnum.symm j).val).prodMk
        (contDiffAt_pi.mpr fun j ↦ contDiffAt_rawBoundary hdim x o ho q j)
  exact hf.comp w (faceTangent (axis hdim x o)).contDiff.contDiffAt

/-- An actual inverse-function-theorem chart, restricted to the literal Stokes
face source. No coordinate equivalence is supplied as a hypothesis. -/
def localChart : OpenPartialHomeomorph (Coord r) (Product x o ho) :=
  ((hasStrictFDerivAt_map hdim x o ho z).toOpenPartialHomeomorph (map hdim x o ho z)).restrOpen
    (smoothSource hdim x o ho z) (isOpen_smoothSource hdim x o ho z)

theorem self_mem_localChart_source : z.val ∈ (localChart hdim x o ho z).source :=
  ⟨(hasStrictFDerivAt_map hdim x o ho z).mem_toOpenPartialHomeomorph_source, self_mem_smoothSource hdim x o ho z⟩

@[simp] theorem localChart_apply (w : Coord r) :
    localChart hdim x o ho z w = map hdim x o ho z w := rfl

theorem localChart_source_subset : (localChart hdim x o ho z).source ⊆ Source hdim x o :=
  fun _ hw ↦ hw.2.1

/-- The topological inverse is exactly the proved scalar native DR inverse. -/
theorem localChart_symm_eq {p : Product x o ho} (hp : p ∈ (localChart hdim x o ho z).target) :
    (localChart hdim x o ho z).symm p = PairedForestProductOverlap.inverse hdim x o ho p := by
  have hw := (localChart hdim x o ho z).map_target hp
  have hs := localChart_source_subset hdim x o ho z hw
  have h := inverse_toProduct hdim x o ho (phase hdim x o ho z) ⟨(localChart hdim x o ho z).symm p, hs⟩
  change PairedForestProductOverlap.inverse hdim x o ho
    (localChart hdim x o ho z ((localChart hdim x o ho z).symm p)) = _ at h
  rw [(localChart hdim x o ho z).right_inv hp] at h
  exact h.symm


theorem localChart_contDiffAt {w : Coord r} (hw : w ∈ (localChart hdim x o ho z).source) :
    ContDiffAt ℝ ⊤ (localChart hdim x o ho z) w :=
  contDiffAt_map hdim x o ho z hw.2

theorem localChart_inverse_contDiffAt {p : Product x o ho} (hp : p ∈ (localChart hdim x o ho z).target) :
    ContDiffAt ℝ ⊤ (PairedForestProductOverlap.inverse hdim x o ho) p := by
  have hs := localChart_source_subset hdim x o ho z ((localChart hdim x o ho z).map_target hp)
  have h := contDiffAt_inverse hdim x o ho (phase hdim x o ho z)
    ⟨(localChart hdim x o ho z).symm p, hs⟩
  change ContDiffAt ℝ ⊤ _ (localChart hdim x o ho z ((localChart hdim x o ho z).symm p)) at h
  rwa [(localChart hdim x o ho z).right_inv hp] at h


theorem localChart_differential_leftInverse {w : Coord r}
    (hw : w ∈ (localChart hdim x o ho z).source) :
    (fderiv ℝ (PairedForestProductOverlap.inverse hdim x o ho) (localChart hdim x o ho z w)).comp
      (fderiv ℝ (localChart hdim x o ho z) w) = ContinuousLinearMap.id ℝ (Coord r) := by
  have hs := localChart_source_subset hdim x o ho z hw
  have hi := contDiffAt_inverse hdim x o ho (phase hdim x o ho z) ⟨w, hs⟩
  have hf := localChart_contDiffAt hdim x o ho z hw
  have hd := (hi.differentiableAt (by simp)).hasFDerivAt.comp w (hf.differentiableAt (by simp)).hasFDerivAt
  have he : (PairedForestProductOverlap.inverse hdim x o ho ∘ localChart hdim x o ho z) =ᶠ[𝓝 w] id :=
    Filter.eventuallyEq_of_mem ((ForestRadialFaceImmersion.isOpen_source hdim x o).mem_nhds hs)
      (fun q hq ↦ inverse_toProduct hdim x o ho (phase hdim x o ho z) ⟨q, hq⟩)
  have hd' := hd.fderiv
  change (PairedForestProductOverlap.inverse hdim x o ho ∘ toProduct hdim x o ho (phase hdim x o ho z)) =ᶠ[𝓝 w] id at he
  rw [he.fderiv_eq, fderiv_id] at hd'
  exact hd'.symm

theorem localChart_differential_bijective {w : Coord r}
    (hw : w ∈ (localChart hdim x o ho z).source) :
    Function.Bijective (fderiv ℝ (localChart hdim x o ho z) w) := by
  have hi : Function.LeftInverse
      (fderiv ℝ (PairedForestProductOverlap.inverse hdim x o ho) (localChart hdim x o ho z w))
      (fderiv ℝ (localChart hdim x o ho z) w) := fun v ↦
    congrArg (fun L : Coord r →L[ℝ] Coord r ↦ L v) (localChart_differential_leftInverse hdim x o ho z hw)
  have hdim' : Module.finrank ℝ (Coord r) = Module.finrank ℝ (Product x o ho) := by
    rw [finrank_product hdim]
    simp [Coord]
  exact ⟨hi.injective, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim').mp hi.injective⟩

end EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestProductChart
