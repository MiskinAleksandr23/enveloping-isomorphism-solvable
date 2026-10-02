import EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestGraphFormOverlap
import EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestCanonicalMarks

/-! Intrinsic canonical labels and branch-independent reassembly of the actual
paired face. Local angle branches may differ by integral turns. The exact
signed sum is independent of any countable measurable subordinate partition;
no individual weighted graph integral is asserted to vanish. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestIntrinsicReassembly
open Configuration BoxStokes PairedForestSimpleCluster PairedForestSmoothProduct
open PairedForestProductChart PairedForestOverlapJacobian PairedForestGraphFormOverlap
open PairedForestCanonicalMarks ForestRadialFaceClassification MeasureTheory Set
open scoped Classical
variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r + 1)
  (x : Compactification (0 : Fin (n + 1)) m) (o : ForestRadialFaceClassification.Orbit 0 x)
  (ho : kind 0 x o = .paired)

/-- Product-coordinate types have the same canonical marked labels whenever
the underlying paired cluster labels agree. -/
theorem product_eq_of_labels_eq
    (y : Compactification (0 : Fin (n + 1)) m) (p : ForestRadialFaceClassification.Orbit 0 y)
    (hp : kind 0 y p = .paired) (h : S x o ho = S y p hp) :
    Product x o ho = Product y p hp := by
  unfold Product
  rw [anchor_eq_of_labels_eq x o ho y p hp h,
    reference_eq_of_labels_eq x o ho y p hp h, h]

/-- The phase reference only changes the real angle by an integral full turn. -/
theorem angle_eq_add_int_period (u v : Circle) (w : Source hdim x o) :
    ∃ k : ℤ, angle hdim x o ho u (facePoint hdim x o w) =
      angle hdim x o ho v (facePoint hdim x o w) + k * (2 * Real.pi) := by
  apply Circle.exp_eq_exp.mp
  apply Subtype.ext
  have h := (circleParameter_angle hdim x o ho u w).trans
    (circleParameter_angle hdim x o ho v w).symm
  simpa only [circleParameter_eq] using h

/-- Shape and coarse coordinates are literally independent of the phase branch. -/
theorem localChart_shape_coarse_eq (z z' : Source hdim x o) (w : Coord r) :
    (localChart hdim x o ho z w).1.2 = (localChart hdim x o ho z' w).1.2 ∧
      (localChart hdim x o ho z w).2 = (localChart hdim x o ho z' w).2 := by
  simp only [localChart_apply, map, toProduct, fullToProduct, and_self]

theorem localChart_angle_eq_add_int_period (z z' : Source hdim x o)
    (w : Source hdim x o) :
    ∃ k : ℤ, (localChart hdim x o ho z w.val).1.1 =
      (localChart hdim x o ho z' w.val).1.1 + k * (2 * Real.pi) :=
  angle_eq_add_int_period hdim x o ho (phase hdim x o ho z) (phase hdim x o ho z') w

/-- Changing the phase branch does not change the chart differential. -/
theorem localChart_fderiv_eq (z z' : Source hdim x o) {w : Coord r}
    (hw : w ∈ (localChart hdim x o ho z).source)
    (hw' : w ∈ (localChart hdim x o ho z').source) :
    fderiv ℝ (localChart hdim x o ho z) w = fderiv ℝ (localChart hdim x o ho z') w := by
  let V : Coord r → ℂ := fun q ↦ rawVelocity hdim x o ho (reference x o ho)
    (faceEmbedding (axis hdim x o) 0 q)
  have hV : DifferentiableAt ℝ V w :=
    ((contDiffAt_rawVelocity hdim x o ho ⟨w, localChart_source_subset hdim x o ho z hw⟩
      (reference x o ho)).differentiableAt (by simp)).comp w
        (hasFDerivAt_faceEmbedding (axis hdim x o) 0 w).differentiableAt
  have ha := ((hasFDerivAt_rotatedAnglePotential
    (inv_ne_zero (phase hdim x o ho z).coe_ne_zero) hw.2.2).comp w hV.hasFDerivAt).const_add
      (Complex.arg (phase hdim x o ho z : ℂ))
  have ha' := ((hasFDerivAt_rotatedAnglePotential
    (inv_ne_zero (phase hdim x o ho z').coe_ne_zero) hw'.2.2).comp w hV.hasFDerivAt).const_add
      (Complex.arg (phase hdim x o ho z' : ℂ))
  have hD := ((localChart_contDiffAt hdim x o ho z hw).differentiableAt (by simp)).hasFDerivAt
  have hf := (ha.prodMk hD.fst.snd).prodMk hD.snd
  have hf' := (ha'.prodMk hD.fst.snd).prodMk hD.snd
  change HasFDerivAt (localChart hdim x o ho z) _ w at hf
  change HasFDerivAt (localChart hdim x o ho z') _ w at hf'
  exact hf.fderiv.trans hf'.fderiv.symm

/-- The actual signed Cartesian Jacobian is branch independent on overlaps. -/
theorem localChart_jacobian_eq (z z' : Source hdim x o) {w : Coord r}
    (hw : w ∈ (localChart hdim x o ho z).source)
    (hw' : w ∈ (localChart hdim x o ho z').source) :
    PairedForestCartesianChange.jacobian hdim x o ho z w =
      PairedForestCartesianChange.jacobian hdim x o ho z' w := by
  have hD := ((PairedForestCartesianChange.cartesian hdim x o ho).symm.hasFDerivAt.comp w
    ((localChart_contDiffAt hdim x o ho z hw).differentiableAt (by simp)).hasFDerivAt).fderiv
  have hD' := ((PairedForestCartesianChange.cartesian hdim x o ho).symm.hasFDerivAt.comp w
    ((localChart_contDiffAt hdim x o ho z' hw').differentiableAt (by simp)).hasFDerivAt).fderiv
  change fderiv ℝ (PairedForestCartesianChange.chart hdim x o ho z) w = _ at hD
  change fderiv ℝ (PairedForestCartesianChange.chart hdim x o ho z') w = _ at hD'
  unfold PairedForestCartesianChange.jacobian
  rw [hD, hD', localChart_fderiv_eq hdim x o ho z z' hw hw']

/-- The original ambient cutoff is independent of the local phase branch. -/
theorem localChart_productCutoff_eq (z z' : Source hdim x o)
    (ρ : OriginalPartitionCancellation.Ambient n m → ℝ) (w : Source hdim x o) :
    productCutoff x o ho ρ (localChart hdim x o ho z w.val) =
      productCutoff x o ho ρ (localChart hdim x o ho z' w.val) :=
  (productCutoff_toProduct hdim x o ho ρ (phase hdim x o ho z) w).trans
    (productCutoff_toProduct hdim x o ho ρ (phase hdim x o ho z') w).symm

/-- The literal graph density transforms consistently on every chart overlap,
retaining the signed Jacobian and original edge order. -/
theorem localChart_graphDensity_overlap (z z' : Source hdim x o)
    (edges : Fin r → GraphForms.Edge n m)
    (hloop : ∀ j, (edges j).target ≠ Sum.inl (edges j).source)
    {w : Coord r} (hw : w ∈ (localChart hdim x o ho z).source)
    (hw' : w ∈ (localChart hdim x o ho z').source) :
    PairedForestCartesianChange.jacobian hdim x o ho z w *
        PairedForestProductGraphDensity.productDensity hdim x o ho edges (localChart hdim x o ho z w) =
      PairedForestCartesianChange.jacobian hdim x o ho z' w *
        PairedForestProductGraphDensity.productDensity hdim x o ho edges (localChart hdim x o ho z' w) :=
  (native_graphDensity_eq_jacobian hdim x o ho z hw edges hloop).symm.trans
    (native_graphDensity_eq_jacobian hdim x o ho z' hw' edges hloop)

/-- The simple graph coefficient itself is independent of local angle branch
on overlapping chart sources, including every edge and its original order. -/
theorem localChart_graphDensity_eq (z z' : Source hdim x o)
    (edges : Fin r → GraphForms.Edge n m)
    (hloop : ∀ j, (edges j).target ≠ Sum.inl (edges j).source)
    {w : Coord r} (hw : w ∈ (localChart hdim x o ho z).source)
    (hw' : w ∈ (localChart hdim x o ho z').source) :
    PairedForestProductGraphDensity.productDensity hdim x o ho edges (localChart hdim x o ho z w) =
      PairedForestProductGraphDensity.productDensity hdim x o ho edges (localChart hdim x o ho z' w) := by
  apply mul_left_cancel₀ (PairedForestCartesianChange.jacobian_ne_zero hdim x o ho z hw)
  have h := localChart_graphDensity_overlap hdim x o ho z z' edges hloop hw hw'
  rwa [← localChart_jacobian_eq hdim x o ho z z' hw hw'] at h

open ForestGlobalGraphStokes ForestRadialFaceLocalization ForestOrthantRealization
open OrientedFormChangeVariables
variable (ρ : OriginalPartitionCancellation.Ambient n m → ℝ)
  (edges : Fin r → GraphForms.Edge n m)
  (hloop : ∀ j, (edges j).target ≠ Sum.inl (edges j).source)
  (κ : Ambient 0 x → ℝ)
  (hmatch : LocalizationAgreement x ρ edges hloop κ)
  (hρ : tsupport (CompactDRAmbientPartition.cutoff 0 ρ) ⊆ (ForestChartOrientation.smallChart 0 x).target)
  (ε : ℝ) (hε : ∀ y ∈ positiveRegion hdim x,
    ε * jacobian (chart hdim x) y = |jacobian (chart hdim x) y|)
include hmatch hρ hε

/-- Actual graph-density CV on any measurable portion of any constructed chart. -/
theorem signed_integral_eq (z : Source hdim x o) (s : Set (Coord r))
    (hs : MeasurableSet s) (hsub : s ⊆ (localChart hdim x o ho z).source) :
    (ε * -((-1 : ℝ) ^ (axis hdim x o).val)) *
      (∫ w in s, NativePairedFaceIntegration.nativeDensity hdim x o ρ edges hloop κ w) =
      productFaceSign hdim x o ho * (∫ p in localChart hdim x o ho z '' s,
        productCutoff x o ho ρ p * PairedForestProductGraphDensity.productDensity hdim x o ho edges p) := by
  have heq := setIntegral_congr_fun (μ := volume) hs (fun w hw ↦
    nativeDensity_eq_jacobian hdim x o ho z (hsub hw) ρ edges hloop κ hmatch)
  rw [heq]
  exact signed_integral_weighted_image hdim x o ho z s hs hsub ρ hρ ε hε _

/-- Countable measurable reassembly for any disjoint partition of the entire
native source subordinate to the actual charts. Every local integral retains
its cutoff, and only the full sum is identified with the native contribution. -/
theorem hasSum_graphIntegral_partition
    (hω : ContDiff ℝ 1 (localForm hdim x ρ edges hloop κ))
    (hc : HasCompactSupport (localForm hdim x ρ edges hloop κ))
    {J : Type*} [Countable J] (center : J → Source hdim x o) (s : J → Set (Coord r))
    (hs : ∀ j, MeasurableSet (s j)) (hdis : Pairwise (fun j k ↦ Disjoint (s j) (s k)))
    (hsub : ∀ j, s j ⊆ (localChart hdim x o ho (center j)).source)
    (hcover : (⋃ j, s j) = Source hdim x o) :
    HasSum (fun j ↦ productFaceSign hdim x o ho *
      (∫ p in localChart hdim x o ho (center j) '' s j,
        productCutoff x o ho ρ p * PairedForestProductGraphDensity.productDensity hdim x o ho edges p))
      (ε * contribution hdim x (localForm hdim x ρ edges hloop κ) o) := by
  have hn := NativePairedFaceIntegration.integrableOn_nativeDensity hdim x o ρ edges hloop κ hω hc
  change IntegrableOn (NativePairedFaceIntegration.nativeDensity hdim x o ρ edges hloop κ) (Source hdim x o) at hn
  have h := (hasSum_integral_iUnion hs hdis (show IntegrableOn
    (NativePairedFaceIntegration.nativeDensity hdim x o ρ edges hloop κ) (⋃ j, s j) from hcover.symm ▸ hn)).mul_left
      (ε * -((-1 : ℝ) ^ (axis hdim x o).val))
  have heq := fun j ↦ signed_integral_eq hdim x o ho ρ edges hloop κ hmatch hρ ε hε (center j) (s j) (hs j) (hsub j)
  simp only [heq, hcover] at h
  rw [contribution_eq_integral_source hdim x o ρ edges hloop κ hmatch]
  simpa only [NativePairedFaceIntegration.nativeDensity, smul_eq_mul, mul_assoc] using h

end EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestIntrinsicReassembly
