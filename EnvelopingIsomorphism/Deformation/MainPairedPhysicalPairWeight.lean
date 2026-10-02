import EnvelopingIsomorphism.Deformation.MainBinaryEdgeRelabelling
import EnvelopingIsomorphism.Deformation.MainPairedBinaryEdges
import EnvelopingIsomorphism.Deformation.Kontsevich.TwoPointFaceRelabelling
import EnvelopingIsomorphism.Deformation.Kontsevich.TwoPointBinaryUnconditionalWeight

/-! Actual two-point integrals for every unordered physical pair, retaining
the original normalization anchor and the original binary edge order. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.MainPairedPhysicalPairWeight
open Kontsevich UniformBinaryGraphs MainScalarBoundaryAssembly
open InteriorGraphFaceCoordinates TwoPointBinaryFaceAdmissibility
open GraphCurvatureLabelCounting GraphCurvaturePhysicalPairs
open scoped Classical
variable {n : ℕ} {i a b : Fin (n+2)} {S : Finset (Fin (n+2))}
  (ha : a ∈ S) (hb : b ∈ S) (hba : b ≠ a) (hi : i ∈ S → a = i)

include ha hb hba hi in
theorem nativeDegree_eq : shapeDegree a b S + coarseDegree i a S 3 =
    GraphForms.dimension (n+1) 2 := by
  rw [totalDegree_eq ha hb hba hi]
  simp [GraphForms.dimension]
  omega

def nativeEdges (H : BinaryGraph (n+2) 3) :
    Fin (shapeDegree a b S + coarseDegree i a S 3) → Edge (n+2) 3 :=
  fun j => let e := mainEdges H (finCongr (nativeDegree_eq ha hb hba hi) j)
    (e.source,e.target)

theorem nativeEdges_noLoops (H : BinaryGraph (n+2) 3)
    (j : Fin (shapeDegree a b S + coarseDegree i a S 3)) :
    (nativeEdges ha hb hba hi H j).2 ≠ Sum.inl (nativeEdges ha hb hba hi H j).1 :=
  mainEdges_noLoops H _

def nativeRows (σ : Equiv.Perm (Fin (n+2))) :
    Equiv.Perm (Fin (shapeDegree a b S + coarseDegree i a S 3)) :=
  (finCongr (nativeDegree_eq ha hb hba hi)).symm.permCongr (MainBinaryEdgeRelabelling.rows σ)

theorem nativeRows_sign (σ : Equiv.Perm (Fin (n+2))) :
    (nativeRows ha hb hba hi σ).sign = 1 := by
  rw [nativeRows, Equiv.Perm.sign_permCongr, MainBinaryEdgeRelabelling.rows_sign]

variable (σ : Equiv.Perm (Fin (n+2))) {T : Finset (Fin (n+2))}
    (hST : ∀ j, σ j ∈ T ↔ j ∈ S)

include hi hST in
theorem anchor_relabel : σ i ∈ T → σ a = σ i := by
  intro h
  exact congrArg σ (hi ((hST i).mp h))

theorem nativeEdges_relabel (H : BinaryGraph (n+2) 3) :
    nativeEdges ((hST a).mpr ha) ((hST b).mpr hb) (σ.injective.ne hba)
      (anchor_relabel hi σ hST) (H.permuteInternal σ) =
    TwoPointFaceRelabelling.edges σ hST
      (fun j => nativeEdges ha hb hba hi H (nativeRows ha hb hba hi σ j)) := by
  funext j
  unfold nativeEdges
  rw [MainBinaryEdgeRelabelling.mainEdges_permuteInternal]
  unfold TwoPointFaceRelabelling.edges InteriorFaceLabelRelabelling.relabelEdge
    nativeRows Equiv.permCongr
  dsimp only [Equiv.trans_apply]
  congr 2

include ha hb hba hi in
theorem integral_nativeEdges_relabel (H : BinaryGraph (n+2) 3) (hS : S.card = 2) :
    TwoPointFaceRelabelling.integral
      (nativeEdges ((hST a).mpr ha) ((hST b).mpr hb) (σ.injective.ne hba)
        (anchor_relabel hi σ hST) (H.permuteInternal σ)) =
      TwoPointFaceRelabelling.integral (nativeEdges ha hb hba hi H) := by
  rw [nativeEdges_relabel ha hb hba hi σ hST H,
    TwoPointFaceRelabelling.integral_edges σ hST _ ha hb hba hS
      (fun j => nativeEdges_noLoops ha hb hba hi H _),
    TwoPointFaceRelabelling.integral_permute, nativeRows_sign, Units.val_one, Int.cast_one, one_mul]

def normalized (H : BinaryGraph (n+2) 3) : ℝ :=
  GeometricWeights.outgoingFactor (fun _ : Fin (n+2) => 2) *
    (((2 * Real.pi) ^ (GraphForms.dimension (n+1) 2))⁻¹ *
      TwoPointFaceRelabelling.integral (nativeEdges ha hb hba hi H))

include ha hb hba hi in
theorem normalized_relabel (H : BinaryGraph (n+2) 3) (hS : S.card = 2) :
    normalized ((hST a).mpr ha) ((hST b).mpr hb) (σ.injective.ne hba)
      (anchor_relabel hi σ hST) (H.permuteInternal σ) = normalized ha hb hba hi H := by
  unfold normalized
  rw [integral_nativeEdges_relabel ha hb hba hi σ hST H hS]

theorem nativeEdges_cluster (v : Fin (n+1)) (H : BinaryGraph (n+2) 3)
    {i a b : Fin (n+2)} (ha : a ∈ cluster v) (hb : b ∈ cluster v)
    (hba : b ≠ a) (hi : i ∈ cluster v → a = i) :
    nativeEdges ha hb hba hi H = TwoPointBinaryFaceAdmissibility.orderedEdges H
      (TwoPointBinaryFaceWeight.sourceMajorOrder v ha hb hba hi) := by
  funext j
  unfold nativeEdges mainEdges TwoPointBinaryFaceAdmissibility.orderedEdges
    TwoPointBinaryFaceWeight.sourceMajorOrder GeometricWeights.canonicalOrder
    UniformBinaryQuotientOrderSign.binaryOrder
  congr 1

theorem normalized_cluster (v : Fin (n+1)) (H : BinaryGraph (n+2) 3)
    {i a b : Fin (n+2)} (ha : a ∈ cluster v) (hb : b ∈ cluster v)
    (hba : b ≠ a) (hi : i ∈ cluster v → a = i) :
    normalized ha hb hba hi H = TwoPointBinaryFaceWeight.normalizedIntegral v H
      (TwoPointBinaryFaceWeight.sourceMajorOrder v ha hb hba hi) := by
  unfold normalized TwoPointBinaryFaceWeight.normalizedIntegral
  rw [nativeEdges_cluster v H ha hb hba hi]
  have hd := nativeDegree_eq ha hb hba hi
  congr 2
  exact congrArg (fun d => ((2 * Real.pi) ^ d)⁻¹) hd.symm

theorem cluster_eq_childPair (v : Fin (n+1)) : cluster v = childPair v := by
  ext j
  simp [cluster, childPair, Fin.exists_fin_two, eq_comm]

theorem physicalCoefficient_representative (H : BinaryGraph (n+2) 3)
    (T : PhysicalPair n) (D : PairLabelFiber T) :
    physicalCoefficient (H.permuteInternal D.val.2.symm) (movedPair D.val.1 (Equiv.refl _)) =
      physicalCoefficient H T := by
  have h := coefficient_eq_physical (H.permuteInternal D.val.2.symm)
    (movedPair D.val.1 (Equiv.refl _)) ⟨(D.val.1,Equiv.refl _),rfl⟩
  simp only [Equiv.refl_symm, KontsevichGraph.General.Graph.permuteInternal_refl] at h
  exact h.symm.trans (coefficient_eq_physical H T D)

/-- Every physical pair has the actual normalized face weight prescribed by
the genuine extracted curvature quotient, including inadmissible graphs. -/
theorem normalized_eq_physicalCoefficient (H : BinaryGraph (n+2) 3) (hS : S.card = 2) :
    normalized ha hb hba hi H = (3 / 2 : ℝ) * physicalCoefficient H ⟨S,hS⟩ := by
  let D := representative (⟨S,hS⟩ : PhysicalPair n)
  let π := D.val.2.symm
  have hp : ∀ j, π j ∈ cluster D.val.1 ↔ j ∈ S := by
    intro j
    rw [cluster_eq_childPair]
    have hh := (movedPair_eq_iff D.val.1 D.val.2 ⟨S,hS⟩).mp D.property (π j)
    simpa only [π, Equiv.apply_symm_apply] using hh.symm
  rw [← normalized_relabel ha hb hba hi π hp H hS]
  rw [normalized_cluster D.val.1 (H.permuteInternal π) ((hp a).mpr ha) ((hp b).mpr hb)
    (π.injective.ne hba) (anchor_relabel hi π hp)]
  rw [TwoPointBinaryUnconditionalWeight.normalized_integral_eq_physicalCoefficient]
  rw [physicalCoefficient_representative H ⟨S,hS⟩ D]

theorem nativeEdges_eq_common (H : BinaryGraph (n+2) 3)
    {a b : Fin (n+2)} {S : Finset (Fin (n+2))}
    (ha : a ∈ S) (hb : b ∈ S) (hba : b ≠ a) (hi : (0 : Fin (n+2)) ∈ S → a = 0) :
    nativeEdges ha hb hba hi H =
      PairedForestCommonRealDensity.edges (main_dimension n) ha hb hba hi (mainEdges H) := rfl

/-- The literal common density used by the original finite Stokes partition
has the required coefficient for every physical pair. -/
theorem normalized_common_integral_eq_physicalCoefficient (H : BinaryGraph (n+2) 3)
    {a b : Fin (n+2)} {S : Finset (Fin (n+2))}
    (ha : a ∈ S) (hb : b ∈ S) (hba : b ≠ a) (hi : (0 : Fin (n+2)) ∈ S → a = 0)
    (hS : S.card = 2) :
    GeometricWeights.outgoingFactor (fun _ : Fin (n+2) => 2) *
      (((2 * Real.pi) ^ (GraphForms.dimension (n+1) 2))⁻¹ *
        ∫ y in InteriorFiberAngleSplit.integrationRegion (shapeN a b S) ×ˢ
          GeometricWeights.realDomain (coarseN (0 : Fin (n+2)) a S) 3,
          realFaceDensity
            (PairedForestCommonRealDensity.edges (main_dimension n) ha hb hba hi (mainEdges H)) y) =
      (3 / 2 : ℝ) * physicalCoefficient H ⟨S,hS⟩ :=
  normalized_eq_physicalCoefficient ha hb hba hi H hS

end EnvelopingIsomorphism.Deformation.MainPairedPhysicalPairWeight
