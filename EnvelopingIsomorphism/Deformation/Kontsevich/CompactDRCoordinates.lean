import EnvelopingIsomorphism.Deformation.Kontsevich.AnchorCompactification
import EnvelopingIsomorphism.Deformation.Kontsevich.ForestDirectionRatioCoordinates
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! A finite real ambient embedding of the genuine compactification.
Its coordinate functions extend smoothly in every regular forest chart,
so ambient smooth cutoffs can be used without corner transition hypotheses. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.CompactDRCoordinates

open Configuration ForestDirectionRatioCoordinates
open scoped Topology

abbrev Ambient (n m : ℕ) := (DoubledPair n m → ℂ) × (DoubledTriple n m → ℝ)
abbrev dimension (n m : ℕ) := Module.finrank ℝ (Ambient n m)

def realCoordinates (n m : ℕ) : Ambient n m ≃L[ℝ] (Fin (dimension n m) → ℝ) :=
  (Module.finBasis ℝ (Ambient n m)).equivFunL

def dataEmbedding {n m : ℕ} (d : DRData n m) : Ambient n m :=
  (fun p => (d.1 p : ℂ), fun q => (d.2 q : ℝ))

theorem continuous_dataEmbedding (n m : ℕ) : Continuous (@dataEmbedding n m) := by
  apply Continuous.prodMk
  · exact continuous_pi fun p => continuous_subtype_val.comp ((continuous_apply p).comp continuous_fst)
  · exact continuous_pi fun q => continuous_subtype_val.comp ((continuous_apply q).comp continuous_snd)

theorem dataEmbedding_injective (n m : ℕ) : Function.Injective (@dataEmbedding n m) := by
  intro a b h
  apply Prod.ext
  · funext p
    apply Subtype.ext
    exact congrFun (congrArg Prod.fst h) p
  · funext q
    apply Subtype.ext
    exact congrFun (congrArg Prod.snd h) q

theorem isClosedEmbedding_dataEmbedding (n m : ℕ) :
    Topology.IsClosedEmbedding (@dataEmbedding n m) :=
  (continuous_dataEmbedding n m).isClosedEmbedding (dataEmbedding_injective n m)

def embedding {n m : ℕ} (i : Fin n) (x : Compactification i m) : Fin (dimension n m) → ℝ :=
  realCoordinates n m (dataEmbedding (compactProjectDR x))

theorem continuous_embedding {n m : ℕ} (i : Fin n) : Continuous (embedding (m := m) i) :=
  (realCoordinates n m).continuous.comp
    ((continuous_dataEmbedding n m).comp (continuous_compactProjectDR i))

theorem embedding_injective {n m : ℕ} (i : Fin n) : Function.Injective (embedding (m := m) i) := by
  intro x y h
  apply projectDR_injective_on_compactification i
  exact dataEmbedding_injective n m ((realCoordinates n m).injective h)

theorem isClosedEmbedding_embedding {n m : ℕ} (i : Fin n) :
    Topology.IsClosedEmbedding (embedding (m := m) i) :=
  (continuous_embedding i).isClosedEmbedding (embedding_injective i)

theorem isCompact_range_embedding {n m : ℕ} (i : Fin n) :
    IsCompact (Set.range (embedding (m := m) i)) :=
  isCompact_range (continuous_embedding i)

variable (T : RootedTree) [Fintype T] {n m : ℕ} (leaf : DoubledLabel n m → T)

/-- The ambient coordinate formula is defined also outside the radial orthant;
smoothness is required only at genuine nonnegative regular parameters. -/
def forestAmbient (x : Parameters T) : Ambient n m :=
  (fun p => (direction T leaf x p : ℂ), fun q => ratioValue T leaf x q)

def forestReal (x : Parameters T) : Fin (dimension n m) → ℝ :=
  realCoordinates n m (forestAmbient T leaf x)

theorem forestAmbient_eq (x : Domain T leaf) :
    forestAmbient T leaf x.val = dataEmbedding (resolvedCoordinates T leaf x) := rfl

theorem contDiffAt_forestAmbient (x : Parameters T) (hx : Admissible T leaf x) :
    ContDiffAt ℝ ⊤ (forestAmbient T leaf) x := by
  apply ContDiffAt.prodMk
  · exact contDiffAt_pi.mpr fun p => contDiffAt_direction_coe T leaf x p (hx.2 p)
  · exact contDiffAt_pi.mpr fun q => contDiffAt_ratioValue T leaf x hx q

theorem contDiffAt_forestReal (x : Parameters T) (hx : Admissible T leaf x) :
    ContDiffAt ℝ ⊤ (forestReal T leaf) x :=
  (realCoordinates n m).contDiff.contDiffAt.comp x (contDiffAt_forestAmbient T leaf x hx)

end EnvelopingIsomorphism.Deformation.Kontsevich.CompactDRCoordinates
