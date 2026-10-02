import EnvelopingIsomorphism.Deformation.Kontsevich.ConfigurationTopology
import EnvelopingIsomorphism.Deformation.Kontsevich.Phase
import Mathlib.Topology.Compactification.OnePoint.Basic

/-!
# A concrete compact closure of normalized configurations

The ambient coordinates consist of compactified positions, directions between
all distinct doubled points, and normalized triple distance ratios. The
normalized configuration space embeds with dense image in its compact closure.
Harmonic phases extend continuously by taking quotients of direction entries.

This topological closure is not declared to be a smooth manifold with corners.
Its relation to a full Fulton--MacPherson compactification requires collision
charts and boundary-stratum theorems beyond the definition of a closure.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich

open Configuration Topology Set

variable {n m : ℕ}

/-- Compact positions, all doubled-point directions, and bounded triple ratios. -/
abbrev CompactCoordinateSpace (n m : ℕ) :=
  ((Fin n ⊕ Fin m) → OnePoint ℂ) ×
    (DoubledPair n m → Circle) × (DoubledTriple n m → Set.Icc (0 : ℝ) 1)

instance : CompactSpace (CompactCoordinateSpace n m) := by infer_instance

def compactPositions {i : Fin n} (c : Normalized i m) : (Fin n ⊕ Fin m) → OnePoint ℂ :=
  fun v => (c.val.vertexPoint v : OnePoint ℂ)

theorem isEmbedding_compactPositions (i : Fin n) :
    IsEmbedding (compactPositions : Normalized i m → (Fin n ⊕ Fin m) → OnePoint ℂ) := by
  have hcoord : IsEmbedding (fun c : Normalized i m => c.val.vertexPoint) :=
    isEmbedding_vertexCoordinates.comp IsEmbedding.subtypeVal
  exact (IsEmbedding.piMap (fun _ : Fin n ⊕ Fin m =>
    (OnePoint.isOpenEmbedding_coe (X := ℂ)).isEmbedding)).comp hcoord

def compactCoordinates {i : Fin n} (c : Normalized i m) : CompactCoordinateSpace n m :=
  (compactPositions c,
    (fun p => complexPhase (c.val.pairDifference p)),
    (fun t => c.val.tripleDistanceRatio t))

@[fun_prop] theorem continuous_compactCoordinates (i : Fin n) :
    Continuous (compactCoordinates : Normalized i m → CompactCoordinateSpace n m) := by
  apply Continuous.prodMk (isEmbedding_compactPositions i).continuous
  apply Continuous.prodMk
  · apply continuous_pi
    intro p
    apply continuous_iff_continuousAt.mpr
    intro c
    exact (continuousAt_complexPhase (c.val.pairDifference_ne_zero p)).comp
      (f := fun d : Normalized i m => d.val.pairDifference p) (x := c)
      ((continuous_pairDifference p).comp continuous_subtype_val).continuousAt
  · exact continuous_pi fun t => (continuous_tripleDistanceRatio t).comp continuous_subtype_val

theorem isEmbedding_compactCoordinates (i : Fin n) :
    IsEmbedding (compactCoordinates : Normalized i m → CompactCoordinateSpace n m) :=
  IsEmbedding.of_comp (continuous_compactCoordinates i) continuous_fst
    (isEmbedding_compactPositions i)

/-- The explicit closed subset of the compact ambient coordinate space. -/
def compactificationSet (i : Fin n) (m : ℕ) : Set (CompactCoordinateSpace n m) :=
  closure (Set.range (compactCoordinates : Normalized i m → CompactCoordinateSpace n m))

def Compactification (i : Fin n) (m : ℕ) := compactificationSet i m

instance (i : Fin n) : TopologicalSpace (Compactification i m) :=
  inferInstanceAs (TopologicalSpace (compactificationSet i m))

instance (i : Fin n) : CompactSpace (Compactification i m) :=
  isCompact_iff_compactSpace.mp isClosed_closure.isCompact

instance (i : Fin n) : T2Space (Compactification i m) :=
  inferInstanceAs (T2Space (compactificationSet i m))

/-- The original normalized configurations inside their compact closure. -/
def compactificationEmbedding (i : Fin n) (c : Normalized i m) : Compactification i m :=
  ⟨compactCoordinates c, subset_closure ⟨c, rfl⟩⟩

theorem isEmbedding_compactificationEmbedding (i : Fin n) :
    IsEmbedding (compactificationEmbedding i : Normalized i m → Compactification i m) :=
  (isEmbedding_compactCoordinates i).codRestrict _ _

theorem denseRange_compactificationEmbedding (i : Fin n) :
    DenseRange (compactificationEmbedding i : Normalized i m → Compactification i m) := by
  exact ((denseRange_inclusion_iff subset_closure).mpr (Subset.rfl)).comp
    Set.rangeFactorization_surjective.denseRange (continuous_inclusion subset_closure)

/-- The direction of an edge from an interior source to an original target. -/
def harmonicNumeratorPair (j : Fin n) (v : Fin n ⊕ Fin m) (hv : v ≠ Sum.inl j) :
    DoubledPair n m :=
  ⟨(Sum.inl (Sum.inl j), Sum.inl v), fun h => hv (Sum.inl.inj h).symm⟩

/-- The companion direction whose source is the reflected interior point. -/
def harmonicDenominatorPair (j : Fin n) (v : Fin n ⊕ Fin m) : DoubledPair n m :=
  ⟨(Sum.inr j, Sum.inl v), by simp⟩

/-- A continuous phase on the entire compact closure, computed from two direction entries. -/
def extendedHarmonicPhase {i : Fin n} (j : Fin n) (v : Fin n ⊕ Fin m)
    (hv : v ≠ Sum.inl j) (x : Compactification i m) : Circle :=
  x.val.2.1 (harmonicNumeratorPair j v hv) / x.val.2.1 (harmonicDenominatorPair j v)

@[fun_prop] theorem continuous_extendedHarmonicPhase {i : Fin n} (j : Fin n)
    (v : Fin n ⊕ Fin m) (hv : v ≠ Sum.inl j) :
    Continuous (extendedHarmonicPhase (i := i) j v hv) := by
  unfold extendedHarmonicPhase
  fun_prop

theorem extendedHarmonicPhase_embedding {i : Fin n} (c : Normalized i m)
    (j : Fin n) (v : Fin n ⊕ Fin m) (hv : v ≠ Sum.inl j) :
    extendedHarmonicPhase j v hv (compactificationEmbedding i c) =
      complexPhase (harmonicRatio (c.val.interior j) (c.val.vertexPoint v)) := by
  change complexPhase (c.val.vertexPoint v - (c.val.interior j : ℂ)) /
    complexPhase (c.val.vertexPoint v - Complex.conjCLE (c.val.interior j : ℂ)) = _
  exact (complexPhase_div
    (sub_ne_zero.mpr (fun h => hv (c.val.vertexPoint_injective h)))
    (c.val.vertex_harmonicDenominator_ne_zero j v)).symm

end EnvelopingIsomorphism.Deformation.Kontsevich
