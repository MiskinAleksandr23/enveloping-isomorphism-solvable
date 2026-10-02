import EnvelopingIsomorphism.Deformation.Kontsevich.ExtractedForestOriginalDecode
import EnvelopingIsomorphism.Deformation.Kontsevich.ForestDRCornerInverse
import Mathlib.Topology.OpenPartialHomeomorph.Composition

/-! Actual open forest charts at every compactification point. Decoder
constraints and the forward right identity are extended from genuine original
configurations, with the extraction tree and all references fixed throughout. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Kontsevich.ForestChartOpenImage

open Configuration ExtractedForestParameters ExtractedForestChildShapes ExtractedForestFrames
open ExtractedForestDRReferences ExtractedForestDRRegion
open Filter Set Topology
open scoped Classical

variable {n m : ℕ} (i : Fin n) (x : Compactification i m)

def decoder (y : Compactification i m) : ForestParameterSpace.Ambient (tree i x) :=
  ForestDRInverse.decode (tree i x) (lab i x) (frames i x) (reference i x) (projectDR y.val)

def referenceRegion : Set (Compactification i m) :=
  {y | projectDR y.val ∈ ForestDRInverse.Region (tree i x) (lab i x) (frames i x) (reference i x)}

theorem isOpen_referenceRegion : IsOpen (referenceRegion i x) :=
  (ForestDRInverse.isOpen_region (tree i x) (lab i x) (frames i x) (reference i x)).preimage
    (continuous_projectDR.comp continuous_subtype_val)

theorem continuousAt_decoder (y : Compactification i m) (hy : y ∈ referenceRegion i x) :
    ContinuousAt (decoder i x) y :=
  (ForestDRInverse.continuousAt_decode (tree i x) (lab i x) (frames i x) (reference i x) _ hy).comp
    (f := fun z : Compactification i m => projectDR z.val)
    (continuous_projectDR.comp continuous_subtype_val).continuousAt

/-- Every target in the fixed open reference region decodes to the actual
closed normalized reflected parameter space. -/
theorem decoder_constraints (y : Compactification i m) (hy : y ∈ referenceRegion i x) :
    ForestParameterSpace.Constraints (tree i x) (reflection i x) (frames i x) (decoder i x y) := by
  have hseq := tendsto_normalizedSequence i y
  have hdec := (continuousAt_decoder i x y hy).tendsto.comp hseq
  apply (ForestParameterSpace.isClosed_constraints (tree i x) (reflection i x) (frames i x)).mem_of_tendsto hdec
  have he := hseq.eventually ((isOpen_referenceRegion i x).mem_nhds hy)
  filter_upwards [he] with k hk
  exact ExtractedForestOriginalDecode.decoder_constraints i x (normalizedSequence i y k).val hk

def target : Set (Compactification i m) :=
  referenceRegion i x ∩ {y | ForestChartConfigurations.OpenConditions (shapeData i x) (decoder i x y)}

theorem isOpen_target : IsOpen (target i x) := by
  apply isOpen_iff_mem_nhds.mpr
  intro y hy
  exact Filter.inter_mem ((isOpen_referenceRegion i x).mem_nhds hy.1)
    ((continuousAt_decoder i x y hy.1).preimage_mem_nhds
      ((ForestChartConfigurations.isOpen_openConditions (shapeData i x)).mem_nhds hy.2))

theorem self_mem_target : x ∈ target i x :=
  ⟨mem_globalRegion i x, ExtractedForestChartPoint.decoder_openConditions i x⟩

abbrev ParameterSpace := ForestParameterSpace.Space (tree i x) (reflection i x) (frames i x)

def signs : Set (ParameterSpace i x) :=
  {q | ForestChartConfigurations.OpenConditions (shapeData i x) q.val}

theorem isOpen_signs : IsOpen (signs i x) :=
  (ForestChartConfigurations.isOpen_openConditions (shapeData i x)).preimage continuous_subtype_val

abbrev Source := signs i x

def sourcePoint : Source i x :=
  ⟨⟨ExtractedForestNormalizedPoint.parameters i x, ExtractedForestNormalizedPoint.constraints i x⟩,
    ExtractedForestChartPoint.openConditions i x⟩

def toCorner (q : Source i x) : ForestChartConfigurations.CornerDomain (shapeData i x) :=
  ⟨q.val.val, q.val.property.1, q.val.property.2.2.1, q.property⟩

theorem continuous_toCorner : Continuous (toCorner i x) :=
  (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

def forward (q : Source i x) : Compactification i m :=
  ForestChartConfigurations.compactificationInsertion (shapeData i x) i (toCorner i x q)

theorem continuous_forward : Continuous (forward i x) :=
  (ForestChartConfigurations.continuous_compactificationInsertion (shapeData i x) i).comp
    (continuous_toCorner i x)

theorem forward_sourcePoint : forward i x (sourcePoint i x) = x :=
  ExtractedForestChartCoverage.compactificationInsertion_eq_original i x

def inverse (y : target i x) : Source i x :=
  ⟨⟨decoder i x y.val, decoder_constraints i x y.val y.property.1⟩, y.property.2⟩

theorem continuous_inverse : Continuous (inverse i x) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  apply continuous_iff_continuousAt.mpr
  intro y
  exact (continuousAt_decoder i x y.val y.property.1).comp continuous_subtype_val.continuousAt

theorem originals_dense (y : target i x) :
    y ∈ closure {z : target i x | ∃ c : Normalized i m, compactificationEmbedding i c = z.val} := by
  rw [mem_closure_iff]
  intro V hV hyV
  obtain ⟨W, hW, rfl⟩ := isOpen_induced_iff.mp hV
  obtain ⟨c, hc⟩ := (denseRange_compactificationEmbedding i).exists_mem_open
    (hW.inter (isOpen_target i x)) ⟨y.val, hyV, y.property⟩
  exact ⟨⟨compactificationEmbedding i c, hc.2⟩, hc.1, c, rfl⟩

/-- The actual forward right identity extends from arbitrary original
configurations in this fixed chart by density and closed equality. -/
theorem forward_inverse (y : target i x) : forward i x (inverse i x y) = y.val := by
  have hclosed : IsClosed {z : target i x | forward i x (inverse i x z) = z.val} :=
    isClosed_eq ((continuous_forward i x).comp (continuous_inverse i x)) continuous_subtype_val
  apply closure_minimal _ hclosed (originals_dense i x y)
  rintro z ⟨c, hc⟩
  have hr : directionRatioCoordinates c.val ∈
      ForestDRInverse.Region (tree i x) (lab i x) (frames i x) (reference i x) := by
    have hr := z.property.1
    change projectDR z.val.val ∈ ForestDRInverse.Region (tree i x) (lab i x) (frames i x) (reference i x) at hr
    rw [← hc] at hr
    exact hr
  have he : toCorner i x (inverse i x z) = ExtractedForestOriginalDecode.chartPoint i x c.val hr := by
    apply Subtype.ext
    change decoder i x z.val = _
    rw [← hc]
    exact (ExtractedForestOriginalDecode.chartPoint_eq_decode i x c.val hr).symm
  change ForestChartConfigurations.compactificationInsertion (shapeData i x) i (toCorner i x (inverse i x z)) = z.val
  rw [he, ExtractedForestOriginalDecode.compactificationInsertion_eq_original i x c hr, hc]

/-- The explicit ambient open neighborhood of x is contained in the actual
forward forest-chart image, with no supplied right-inverse/coverage premise. -/
theorem target_subset_range : target i x ⊆ Set.range (forward i x) := by
  intro y hy
  exact ⟨inverse i x ⟨y, hy⟩, forward_inverse i x ⟨y, hy⟩⟩

theorem canonicalLeaf_lab (v : tree i x) (hv : IsMax v) : canonicalLeaf i x (lab i x v) = v := by
  obtain ⟨j, _, hj⟩ := ((extraction i x).tree_leaf_iff_singleton Finset.univ
    ⟨Sum.inr i, Finset.mem_univ _⟩ v).mp hv
  have he : v = canonicalLeaf i x j := Subtype.ext hj
  subst v
  rw [lab_canonicalLeaf]

theorem decoder_forward (q : Source i x) (hq : forward i x q ∈ referenceRegion i x) :
    decoder i x (forward i x q) = q.val.val := by
  have hproj := ForestChartConfigurations.compactificationInsertion_projectDR (shapeData i x) i (toCorner i x q)
  change projectDR (forward i x q).val = ForestChartConfigurations.fullDR (shapeData i x) (toCorner i x q) at hproj
  have hr : ForestChartConfigurations.fullDR (shapeData i x) (toCorner i x q) ∈
      ForestDRInverse.Region (tree i x) (lab i x) (frames i x) (reference i x) := by
    change projectDR (forward i x q).val ∈ ForestDRInverse.Region (tree i x) (lab i x) (frames i x) (reference i x) at hq
    rw [hproj] at hq
    exact hq
  change ForestDRInverse.decode (tree i x) (lab i x) (frames i x) (reference i x)
    (projectDR (forward i x q).val) = _
  rw [hproj]
  exact ForestDRCornerInverse.decode_resolved (tree i x) (reflection i x) (frames i x)
    (canonicalLeaf i x) (lab i x) doubledReflection (reference i x)
    (ExtractedForestChartPoint.stableFixed i x) (referenceModes i x) (canonicalLeaf_lab i x)
    (fun j => (canonicalLeaf_reflect i x j).symm)
    (ForestChartConfigurations.resolvedParameters (shapeData i x) (toCorner i x q)) q.val.property hr

theorem inverse_forward (q : Source i x) (hq : forward i x q ∈ target i x) :
    inverse i x ⟨forward i x q, hq⟩ = q := by
  apply Subtype.ext
  apply Subtype.ext
  exact decoder_forward i x q hq.1

def source : Set (Source i x) := (forward i x) ⁻¹' target i x

theorem isOpen_source : IsOpen (source i x) := (isOpen_target i x).preimage (continuous_forward i x)

theorem sourcePoint_mem_source : sourcePoint i x ∈ source i x := by
  change forward i x (sourcePoint i x) ∈ target i x
  rw [forward_sourcePoint]
  exact self_mem_target i x

/-- A total extension is needed by the native partial-homeomorphism type.
Its values outside the explicit open target are the already constructed source
point and impose no additional mathematical condition. -/
def inverseTotal (y : Compactification i m) : Source i x :=
  if hy : y ∈ target i x then inverse i x ⟨y, hy⟩ else sourcePoint i x

theorem inverseTotal_of_mem (y : Compactification i m) (hy : y ∈ target i x) :
    inverseTotal i x y = inverse i x ⟨y, hy⟩ := by simp [inverseTotal, hy]

theorem continuousOn_inverseTotal : ContinuousOn (inverseTotal i x) (target i x) := by
  apply continuousOn_iff_continuous_restrict.mpr
  convert continuous_inverse i x using 1
  funext y
  exact inverseTotal_of_mem i x y.val y.property

/-- An honest native open partial homeomorphism, with both inverse laws proved
from the actual forest formulas and original-configuration density. -/
def openPartialHomeomorph : OpenPartialHomeomorph (Source i x) (Compactification i m) where
  toFun := forward i x
  invFun := inverseTotal i x
  source := source i x
  target := target i x
  map_source' := fun _ hq => hq
  map_target' := by
    intro y hy
    change forward i x (inverseTotal i x y) ∈ target i x
    rw [inverseTotal_of_mem i x y hy, forward_inverse]
    exact hy
  left_inv' := by
    intro q hq
    rw [inverseTotal_of_mem i x _ hq, inverse_forward]
  right_inv' := by
    intro y hy
    rw [inverseTotal_of_mem i x y hy, forward_inverse]
  continuousOn_toFun := (continuous_forward i x).continuousOn
  continuousOn_invFun := continuousOn_inverseTotal i x
  open_source := isOpen_source i x
  open_target := isOpen_target i x

theorem mem_openPartialHomeomorph_target : x ∈ (openPartialHomeomorph i x).target := self_mem_target i x

/-- Passing through the open sign-subtype inclusion gives an actual open
partial homeomorphism on the full closed normalized parameter space. -/
def parameterChart : OpenPartialHomeomorph (ParameterSpace i x) (Compactification i m) :=
  ((⟨signs i x, isOpen_signs i x⟩ : TopologicalSpace.Opens (ParameterSpace i x)).openPartialHomeomorphSubtypeCoe
    ⟨sourcePoint i x⟩).symm.trans (openPartialHomeomorph i x)

theorem parameterChart_target : (parameterChart i x).target = target i x := by
  simp only [parameterChart, OpenPartialHomeomorph.trans_target,
    OpenPartialHomeomorph.symm_target, TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_source,
    Set.preimage_univ, Set.inter_univ]
  rfl

theorem mem_parameterChart_target : x ∈ (parameterChart i x).target := by
  rw [parameterChart_target]
  exact self_mem_target i x

end EnvelopingIsomorphism.Deformation.Kontsevich.ForestChartOpenImage
