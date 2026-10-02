import EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestCartesianChange
import Mathlib.Topology.Compactness.Lindelof

/-! A countable measurable localization of the entire noncompact strict paired
face. First-chart assignment gives disjoint pieces and weights summing to one;
no derivative of these measurable weights is taken. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestCountableLocalization
open Configuration PairedForestSmoothProduct PairedForestProductChart
open ForestRadialFaceClassification BoxStokes MeasureTheory Set
open scoped Classical Topology
variable {n m r : ℕ} (hdim : GraphForms.dimension n m = r + 1)
  (x : Compactification (0 : Fin (n + 1)) m) (o : ForestRadialFaceClassification.Orbit 0 x)
  (ho : kind 0 x o = .paired)

theorem exists_countable_cover : ∃ c : Set (Source hdim x o), c.Countable ∧
    Source hdim x o ⊆ ⋃ z ∈ c, (localChart hdim x o ho z).source := by
  apply (HereditarilyLindelofSpace.isLindelof (Source hdim x o)).elim_countable_subcover
    (fun z ↦ (localChart hdim x o ho z).source) (fun z ↦ (localChart hdim x o ho z).open_source)
  intro w hw
  exact mem_iUnion.mpr ⟨⟨w, hw⟩, self_mem_localChart_source hdim x o ho ⟨w, hw⟩⟩

def centers : Set (Source hdim x o) := (exists_countable_cover hdim x o ho).choose

instance : Countable (centers hdim x o ho) :=
  (exists_countable_cover hdim x o ho).choose_spec.1.to_subtype

instance : Encodable (centers hdim x o ho) := Encodable.ofCountable _

abbrev Index := centers hdim x o ho

def region (j : Index hdim x o ho) : Set (Coord r) := (localChart hdim x o ho j.val).source

theorem cover : Source hdim x o = ⋃ j : Index hdim x o ho, region hdim x o ho j := by
  apply subset_antisymm
  · intro w hw
    obtain ⟨z, hz, hwz⟩ := mem_iUnion₂.mp ((exists_countable_cover hdim x o ho).choose_spec.2 hw)
    exact mem_iUnion.mpr ⟨⟨z, hz⟩, hwz⟩
  · exact iUnion_subset fun j ↦ localChart_source_subset hdim x o ho j.val

/-- Every point is assigned to its first chart in the countable enumeration. -/
def piece (j : Index hdim x o ho) : Set (Coord r) :=
  region hdim x o ho j \ ⋃ k : Index hdim x o ho, ⋃ (_ : Encodable.encode k < Encodable.encode j), region hdim x o ho k

theorem piece_subset (j : Index hdim x o ho) : piece hdim x o ho j ⊆ (localChart hdim x o ho j.val).source :=
  sdiff_subset

theorem measurableSet_piece (j : Index hdim x o ho) : MeasurableSet (piece hdim x o ho j) :=
  (localChart hdim x o ho j.val).open_source.measurableSet.diff
    (MeasurableSet.iUnion fun k ↦ MeasurableSet.iUnion fun _ ↦ (localChart hdim x o ho k.val).open_source.measurableSet)

theorem pairwiseDisjoint_piece : Pairwise (fun j k ↦ Disjoint (piece hdim x o ho j) (piece hdim x o ho k)) := by
  intro j k hjk
  apply disjoint_left.mpr
  intro w hwj hwk
  have hcode : Encodable.encode j ≠ Encodable.encode k := fun h ↦ hjk (Encodable.encode_injective h)
  rcases lt_or_gt_of_ne hcode with hlt | hgt
  · exact hwk.2 (mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨hlt, hwj.1⟩⟩)
  · exact hwj.2 (mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨hgt, hwk.1⟩⟩)

theorem iUnion_piece : (⋃ j : Index hdim x o ho, piece hdim x o ho j) = Source hdim x o := by
  apply subset_antisymm
  · apply iUnion_subset
    intro j
    exact (piece_subset hdim x o ho j).trans (localChart_source_subset hdim x o ho j.val)
  · intro w hw
    have hex : ∃ a : ℕ, ∃ j : Index hdim x o ho, Encodable.encode j = a ∧ w ∈ region hdim x o ho j := by
      rw [cover hdim x o ho] at hw
      obtain ⟨j, hj⟩ := mem_iUnion.mp hw
      exact ⟨Encodable.encode j, j, rfl, hj⟩
    obtain ⟨j, hj, hwj⟩ := Nat.find_spec hex
    refine mem_iUnion.mpr ⟨j, hwj, ?_⟩
    intro h
    obtain ⟨k, hkj, hwk⟩ := mem_iUnion₂.mp h
    exact Nat.find_min hex (hj ▸ hkj) ⟨k, rfl, hwk⟩

def weight (j : Index hdim x o ho) : Coord r → ℝ := (piece hdim x o ho j).indicator (fun _ ↦ 1)

theorem measurable_weight (j : Index hdim x o ho) : Measurable (weight hdim x o ho j) :=
  measurable_const.indicator (measurableSet_piece hdim x o ho j)

theorem weight_nonneg (j : Index hdim x o ho) (w : Coord r) : 0 ≤ weight hdim x o ho j w := by
  unfold weight
  exact indicator_nonneg (fun _ _ ↦ zero_le_one) w

theorem tsum_weight {w : Coord r} (hw : w ∈ Source hdim x o) :
    ∑' j : Index hdim x o ho, weight hdim x o ho j w = 1 := by
  rw [← iUnion_piece hdim x o ho] at hw
  obtain ⟨j, hj⟩ := mem_iUnion.mp hw
  rw [tsum_eq_single j]
  · exact indicator_of_mem hj _
  · intro k hkj
    exact indicator_of_notMem (fun hk ↦ (pairwiseDisjoint_piece hdim x o ho hkj).le_bot ⟨hk, hj⟩) _

/-- Countable exact native integral decomposition, with no finite-cover claim. -/
theorem hasSum_integral_piece (f : Coord r → ℝ) (hf : IntegrableOn f (Source hdim x o)) :
    HasSum (fun j : Index hdim x o ho ↦ ∫ w in piece hdim x o ho j, f w)
      (∫ w in Source hdim x o, f w) := by
  have hu := iUnion_piece hdim x o ho
  have h := hasSum_integral_iUnion (measurableSet_piece hdim x o ho)
    (pairwiseDisjoint_piece hdim x o ho) (show IntegrableOn f (⋃ j, piece hdim x o ho j) from hu.symm ▸ hf)
  simpa only [hu] using h

/-- Every local term is transported through the proved actual chart, so this
series gives the whole native face integral in genuine product coordinates. -/
theorem hasSum_integral_product (f : Coord r → ℝ) (hf : IntegrableOn f (Source hdim x o)) :
    HasSum (fun j : Index hdim x o ho ↦
      ∫ p in localChart hdim x o ho j.val '' piece hdim x o ho j,
        PairedForestCartesianChange.pushforward hdim x o ho j.val f p)
      (∫ w in Source hdim x o, f w) := by
  have h := hasSum_integral_piece hdim x o ho f hf
  convert h using 1
  funext j
  exact PairedForestCartesianChange.integral_pushforward hdim x o ho j.val _
    (measurableSet_piece hdim x o ho j) (piece_subset hdim x o ho j) f


theorem integrableOn_product_piece (f : Coord r → ℝ) (hf : IntegrableOn f (Source hdim x o))
    (j : Index hdim x o ho) :
    IntegrableOn (PairedForestCartesianChange.pushforward hdim x o ho j.val f)
      (localChart hdim x o ho j.val '' piece hdim x o ho j) :=
  (PairedForestCartesianChange.integrableOn_pushforward_iff hdim x o ho j.val _
    (measurableSet_piece hdim x o ho j) (piece_subset hdim x o ho j) f).mpr
      (hf.mono_set ((piece_subset hdim x o ho j).trans (localChart_source_subset hdim x o ho j.val)))

theorem summable_integral_product (f : Coord r → ℝ) (hf : IntegrableOn f (Source hdim x o)) :
    Summable (fun j : Index hdim x o ho ↦
      ∫ p in localChart hdim x o ho j.val '' piece hdim x o ho j,
        PairedForestCartesianChange.pushforward hdim x o ho j.val f p) :=
  (hasSum_integral_product hdim x o ho f hf).summable

theorem integral_eq_tsum_product (f : Coord r → ℝ) (hf : IntegrableOn f (Source hdim x o)) :
    (∫ w in Source hdim x o, f w) = ∑' j : Index hdim x o ho,
      ∫ p in localChart hdim x o ho j.val '' piece hdim x o ho j,
        PairedForestCartesianChange.pushforward hdim x o ho j.val f p :=
  (hasSum_integral_product hdim x o ho f hf).tsum_eq.symm

end EnvelopingIsomorphism.Deformation.Kontsevich.PairedForestCountableLocalization
