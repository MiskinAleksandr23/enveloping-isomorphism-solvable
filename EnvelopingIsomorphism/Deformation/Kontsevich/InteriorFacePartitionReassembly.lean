import EnvelopingIsomorphism.Deformation.Kontsevich.InteriorGraphFaceIntegral
import EnvelopingIsomorphism.Deformation.Kontsevich.FiniteOrientedForestPartition

/-! Reassembly of the genuine finite ambient forest partition on the actual
simple interior face. The weights are only pulled back, bounded, and integrated;
no derivatives of the weights are taken. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Kontsevich.InteriorFacePartitionReassembly
open InteriorGraphFaceCoordinates InteriorFiberAngleSplit Set MeasureTheory
open scoped Classical Manifold ContDiff

variable {n m : ℕ} {i a b : Fin (n + 1)} {S : Finset (Fin (n + 1))}

abbrev FaceRegion (i a b : Fin (n + 1)) (S : Finset (Fin (n + 1))) (m : ℕ) :
    Set (RealProductCoordinates i a b S m) :=
  integrationRegion (shapeN a b S) ×ˢ GeometricWeights.realDomain (coarseN i a S) m

theorem measurableSet_faceRegion : MeasurableSet (FaceRegion i a b S m) :=
  (measurableSet_integrationRegion _).prod (GeometricWeights.measurableSet_realDomain _ _)

def toAngularDomain (ha : a ∈ S) (hba : b ≠ a) (x : FaceRegion i a b S m) :
    ClusterAngularDomain i a b S m :=
  ⟨toAngularReal x.val, by exact ⟨le_rfl,
    openConditions_toAngular ha hba (toProduct x.val) x.property.1.2 x.property.2⟩⟩

theorem continuous_toAngularDomain (ha : a ∈ S) (hba : b ≠ a) :
    Continuous (toAngularDomain (i := i) (m := m) ha hba) := by
  apply Continuous.subtype_mk
  exact (contDiff_toAngular.continuous.comp toProduct.continuous).comp continuous_subtype_val

/-- The original compactification point at radius zero of these exact product parameters. -/
def facePoint (ha : a ∈ S) (hb : b ∈ S) (hba : b ≠ a) (hanchor : i ∈ S → a = i)
    (x : FaceRegion i a b S m) : Compactification i m :=
  ClusterAngularDomain.toCompactification ha hb hba hanchor (toAngularDomain ha hba x)

theorem continuous_facePoint (ha : a ∈ S) (hb : b ∈ S) (hba : b ≠ a) (hanchor : i ∈ S → a = i) :
    Continuous (facePoint (m := m) ha hb hba hanchor) :=
  NormalizedInteriorClusterSlice.continuous_insertion.comp
    ((ClusterAngularDomain.isLocalHomeomorph_toSlice ha hb hba hanchor).continuous.comp
      (continuous_toAngularDomain ha hba))

abbrev Partition (J : Type*) (i : Fin (n + 1)) (m : ℕ) :=
  SmoothPartitionOfUnity J 𝓘(ℝ, CompactDRAmbientPartition.Euclidean (n := n + 1) (m := m))
    (CompactDRAmbientPartition.Euclidean (n := n + 1) (m := m))
    (range (CompactDRCoordinates.embedding (m := m) i))

variable {J : Type*} [Fintype J]
variable (ρ : Partition J i m) (ha : a ∈ S) (hb : b ∈ S) (hba : b ≠ a) (hanchor : i ∈ S → a = i)

def weightOnFace (j : J) (x : FaceRegion i a b S m) : ℝ :=
  CompactDRAmbientPartition.cutoff i (ρ j) (facePoint ha hb hba hanchor x)

/-- Zero extension is only for ambient integration; on the face this is the
same global cutoff that occurs in the forest Stokes localizations. -/
def weight (j : J) (x : RealProductCoordinates i a b S m) : ℝ :=
  if hx : x ∈ FaceRegion i a b S m then weightOnFace ρ ha hb hba hanchor j ⟨x, hx⟩ else 0

theorem weight_eq (j : J) (x : RealProductCoordinates i a b S m) (hx : x ∈ FaceRegion i a b S m) :
    weight ρ ha hb hba hanchor j x =
      CompactDRAmbientPartition.cutoff i (ρ j) (facePoint ha hb hba hanchor ⟨x, hx⟩) := by
  simp only [weight, dif_pos hx, weightOnFace]

theorem continuous_weightOnFace (j : J) : Continuous (weightOnFace ρ ha hb hba hanchor j) :=
  (ρ j).property.continuous.comp ((CompactDRCoordinates.continuous_embedding i).comp
    (continuous_facePoint ha hb hba hanchor))

theorem measurable_weight (j : J) : Measurable (weight ρ ha hb hba hanchor j) :=
  Measurable.dite (continuous_weightOnFace ρ ha hb hba hanchor j).measurable
    measurable_const measurableSet_faceRegion

theorem weight_nonneg (j : J) (x : RealProductCoordinates i a b S m) :
    0 ≤ weight ρ ha hb hba hanchor j x := by
  unfold weight
  split_ifs
  · exact ρ.nonneg j _
  · exact le_rfl

theorem weight_le_one (j : J) (x : RealProductCoordinates i a b S m) :
    weight ρ ha hb hba hanchor j x ≤ 1 := by
  unfold weight
  split_ifs
  · exact ρ.le_one j _
  · norm_num

theorem sum_weight (x : RealProductCoordinates i a b S m) (hx : x ∈ FaceRegion i a b S m) :
    ∑ j, weight ρ ha hb hba hanchor j x = 1 := by
  simp_rw [weight_eq ρ ha hb hba hanchor _ x hx, CompactDRAmbientPartition.cutoff]
  simpa only [finsum_eq_sum_of_fintype] using
    ρ.sum_eq_one (mem_range_self (facePoint ha hb hba hanchor ⟨x, hx⟩))

variable (edges : Fin (shapeDegree a b S + coarseDegree i a S m) → Edge (n + 1) m)

def localizedDensity (j : J) (x : RealProductCoordinates i a b S m) : ℝ :=
  weight ρ ha hb hba hanchor j x * realFaceDensity edges x

theorem sum_localizedDensity (x : RealProductCoordinates i a b S m) (hx : x ∈ FaceRegion i a b S m) :
    ∑ j, localizedDensity ρ ha hb hba hanchor edges j x = realFaceDensity edges x := by
  simp only [localizedDensity, ← Finset.sum_mul, sum_weight ρ ha hb hba hanchor x hx, one_mul]

variable (hcount : Fintype.card {q // IsInternal S (edges q)} = shapeDegree a b S)
variable (hlarge : 3 ≤ S.card) (hne : ∀ q, (edges q).2 ≠ Sum.inl (edges q).1)
include hcount hlarge hne

/-- Every actual localized piece is L1 by the proved bound 0≤ρ≤1 and the
unconditional whole-face L1 theorem. No regularity across complex zeros is used. -/
theorem integrableOn_localizedDensity (j : J) :
    IntegrableOn (localizedDensity ρ ha hb hba hanchor edges j) (FaceRegion i a b S m) := by
  have hi := (integral_realFaceDensity_eq_zero edges hcount ha hb hba hlarge hne).1
  exact hi.bdd_mul (measurable_weight ρ ha hb hba hanchor j).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (weight_nonneg ρ ha hb hba hanchor j x)]
      exact weight_le_one ρ ha hb hba hanchor j x)

/-- Finite integral reassembly for the actual ambient partition on this face. -/
theorem sum_integral_localizedDensity :
    (∑ j, ∫ x in FaceRegion i a b S m, localizedDensity ρ ha hb hba hanchor edges j x) =
      ∫ x in FaceRegion i a b S m, realFaceDensity edges x := by
  rw [← integral_finsetSum _ (fun j _ ↦ integrableOn_localizedDensity ρ ha hb hba hanchor edges hcount hlarge hne j)]
  exact setIntegral_congr_fun measurableSet_faceRegion
    (sum_localizedDensity ρ ha hb hba hanchor edges)

/-- The localized integral sum vanishes after reassembly. Individual localized
integrals are not asserted to vanish. -/
theorem sum_integral_localizedDensity_eq_zero :
    (∑ j, ∫ x in FaceRegion i a b S m, localizedDensity ρ ha hb hba hanchor edges j x) = 0 := by
  rw [sum_integral_localizedDensity ρ ha hb hba hanchor edges hcount hlarge hne]
  exact (integral_realFaceDensity_eq_zero edges hcount ha hb hba hlarge hne).2

end EnvelopingIsomorphism.Deformation.Kontsevich.InteriorFacePartitionReassembly
