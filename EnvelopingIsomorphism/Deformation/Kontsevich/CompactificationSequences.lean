import EnvelopingIsomorphism.Deformation.Kontsevich.AnchorCompactification
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Sequences

/-!
# Sequential approximation in the actual compactification

Metrizability is transferred from the finite product of direction and ratio
coordinates through the proved anchor homeomorphism. No metric structure on
`OnePoint ℂ` is required. Density then constructs a sequence of genuine normalized
configurations approaching every point of the compactification.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich

open Configuration Filter Set Topology TopologicalSpace

variable {n m : ℕ}

instance drDataMetrizableSpace : MetrizableSpace (DRData n m) := by
  infer_instance

instance drSpaceMetrizableSpace : MetrizableSpace (DRSpace n m) := by
  change MetrizableSpace (directionRatioSet n m)
  infer_instance

/-- Metrizability of the actual compactification follows from the full
direction/ratio homeomorphism, independently of its position coordinates. -/
instance compactificationMetrizableSpace (i : Fin n) :
    MetrizableSpace (Compactification i m) :=
  (toDRHomeomorph i).isEmbedding.metrizableSpace

theorem compactification_firstCountableTopology (i : Fin n) :
    FirstCountableTopology (Compactification i m) := inferInstance

/-- The actual dense embedding supplies a sequence of normalized configurations
converging to any compactification point. This is a theorem, not input data. -/
theorem exists_normalized_sequence (i : Fin n) (x : Compactification i m) :
    ∃ c : ℕ → Normalized i m,
      Tendsto (fun r => compactificationEmbedding i (c r)) atTop (𝓝 x) := by
  obtain ⟨u, hu, hx⟩ := mem_closure_iff_seq_limit.mp
    (denseRange_compactificationEmbedding i x)
  choose c hc using hu
  refine ⟨c, ?_⟩
  simpa only [hc] using hx

/-- A fixed choice of actual normalized approximants, with convergence proved
below. The choice is made from the preceding density theorem. -/
def normalizedSequence (i : Fin n) (x : Compactification i m) : ℕ → Normalized i m :=
  (exists_normalized_sequence i x).choose

theorem tendsto_normalizedSequence (i : Fin n) (x : Compactification i m) :
    Tendsto (fun r => compactificationEmbedding i (normalizedSequence i x r)) atTop (𝓝 x) :=
  (exists_normalized_sequence i x).choose_spec

/-- Convergence holds in the original complete ambient coordinate space. -/
theorem tendsto_normalizedSequence_coordinates (i : Fin n) (x : Compactification i m) :
    Tendsto (fun r => compactCoordinates (normalizedSequence i x r)) atTop (𝓝 x.val) :=
  continuous_subtype_val.continuousAt.tendsto.comp (tendsto_normalizedSequence i x)

/-- The chosen sequence recovers all full direction/ratio coordinates together. -/
theorem tendsto_normalizedSequence_DR (i : Fin n) (x : Compactification i m) :
    Tendsto (fun r => normalizedDirectionRatios (normalizedSequence i x r)) atTop
      (𝓝 (projectDR x.val)) :=
  continuous_projectDR.continuousAt.tendsto.comp
    (tendsto_normalizedSequence_coordinates i x)

theorem tendsto_normalizedSequence_position (i : Fin n) (x : Compactification i m)
    (v : Fin n ⊕ Fin m) :
    Tendsto (fun r => ((normalizedSequence i x r).val.vertexPoint v : OnePoint ℂ)) atTop
      (𝓝 (x.val.1 v)) := by
  exact ((continuous_apply v).comp continuous_fst).continuousAt.tendsto.comp
    (tendsto_normalizedSequence_coordinates i x)

theorem tendsto_normalizedSequence_direction (i : Fin n) (x : Compactification i m)
    (p : DoubledPair n m) :
    Tendsto (fun r => complexPhase ((normalizedSequence i x r).val.pairDifference p)) atTop
      (𝓝 (x.val.2.1 p)) := by
  exact ((continuous_apply p).comp continuous_fst).continuousAt.tendsto.comp
    (tendsto_normalizedSequence_DR i x)

theorem tendsto_normalizedSequence_ratio (i : Fin n) (x : Compactification i m)
    (t : DoubledTriple n m) :
    Tendsto (fun r => (normalizedSequence i x r).val.tripleDistanceRatio t) atTop
      (𝓝 (x.val.2.2 t)) := by
  exact ((continuous_apply t).comp continuous_snd).continuousAt.tendsto.comp
    (tendsto_normalizedSequence_DR i x)

theorem tendsto_normalizedSequence_ratio_real (i : Fin n) (x : Compactification i m)
    (t : DoubledTriple n m) :
    Tendsto (fun r => ((normalizedSequence i x r).val.tripleDistanceRatio t : ℝ)) atTop
      (𝓝 (x.val.2.2 t : ℝ)) :=
  continuous_subtype_val.continuousAt.tendsto.comp (tendsto_normalizedSequence_ratio i x t)

/-- Applying the genuine affine normalization at another anchor to these same
approximants converges to the proved compactified change of anchor. -/
theorem tendsto_normalizedSequence_changeAnchor (i j : Fin n) (x : Compactification i m) :
    Tendsto (fun r => compactificationEmbedding j
      (normalized j (normalizedSequence i x r).val)) atTop (𝓝 (anchorHomeomorph i j x)) := by
  have h := (anchorHomeomorph i j).continuous.continuousAt.tendsto.comp
    (tendsto_normalizedSequence i x)
  change Tendsto (fun r => anchorHomeomorph i j
    (compactificationEmbedding i (normalizedSequence i x r))) atTop
      (𝓝 (anchorHomeomorph i j x)) at h
  simpa only [anchorHomeomorph_embedding] using h

end EnvelopingIsomorphism.Deformation.Kontsevich
