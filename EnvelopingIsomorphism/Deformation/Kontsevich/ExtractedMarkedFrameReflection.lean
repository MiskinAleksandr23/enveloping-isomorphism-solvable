import EnvelopingIsomorphism.Deformation.Kontsevich.ExtractedMarkedFrameLimits
import EnvelopingIsomorphism.Deformation.Kontsevich.ForestMarkedFrameReflection

/-! Actual reflected marked parameters from every extracted compactification
point, and their limits in the closed real reflected parameter subspace. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Kontsevich.ExtractedMarkedFrameReflection

open Configuration ComplexConjugate Filter Topology
open ForestMarkedFrames ExtractedForestParameters ExtractedForestChildShapes
open ExtractedForestFrames ExtractedMarkedFrameLimits
open scoped Classical

variable {n m : ℕ} (i : Fin n) (x : Compactification i m)

/-- All generic reflection compatibility conditions are proved from the
actual extracted frame selector. -/
theorem compatible : ForestMarkedFrameReflection.Compatible (tree i x) (reflection i x) (frames i x) := by
  constructor
  ·
    intro v hv hs
    have ht := frames_typeCorrect i x v hv
    cases hf : frames i x v hv with
    | complex a b ha hb hne =>
      rw [hf] at ht
      exact False.elim (ht hs)
    | stableHeight a ha => exact Or.inl ⟨a, ha, rfl⟩
    | stableRealPair a b ha hb hne => exact Or.inr ⟨a, b, ha, hb, hne, rfl⟩
  ·
    intro v hv hs
    exact ⟨(markedPair i x v hv).1, (markedPair i x v hv).2,
      (markedPair_spec i x v hv).1, (markedPair_spec i x v hv).2.1,
      (markedPair_spec i x v hv).2.2, frames_nonstable i x v hv hs,
      frames_nonstable_reflection i x v hv hs⟩

theorem input_leaf_reflection (k : ℕ) (v : tree i x) (hv : IsMax v) :
    ExtractedForestParameters.center i x k (reflection i x v) =
      conj (ExtractedForestParameters.center i x k v) := by
  obtain ⟨j, _, hj⟩ := ((extraction i x).tree_leaf_iff_singleton Finset.univ
    ⟨Sum.inr i, Finset.mem_univ _⟩ v).mp hv
  have he : v = canonicalLeaf i x j := Subtype.ext hj
  subst v
  rw [canonicalLeaf_reflect, ExtractedForestParameters.center_leaf, ExtractedForestParameters.center_leaf]
  exact (extraction i x).input_mirror ((extraction i x).subsequence k) j

theorem markedCenter_reflection (k : ℕ) (v : tree i x) :
    markedCenter i x k (reflection i x v) = conj (markedCenter i x k v) :=
  ForestMarkedFrameReflection.center_reflection (tree i x) (reflection i x) (frames i x)
    (compatible i x) _ (input_leaf_reflection i x k) v

theorem markedRadius_reflection (k : ℕ) (v : tree i x) :
    markedRadius i x k (reflection i x v) = markedRadius i x k v :=
  ForestMarkedFrameReflection.radius_reflection (tree i x) (reflection i x) (frames i x)
    (compatible i x) _ (input_leaf_reflection i x k) v

theorem markedLocalRadii_reflection (k : ℕ) (v : tree i x) :
    markedLocalRadii i x k (reflection i x v) = markedLocalRadii i x k v :=
  ForestMarkedFrameReflection.fixedLocalRadii_reflection (tree i x) (reflection i x) (frames i x)
    (compatible i x) _ (input_leaf_reflection i x k) v

theorem markedIncrements_reflection (k : ℕ) (v : tree i x) :
    markedIncrements i x k (reflection i x v) = conj (markedIncrements i x k v) :=
  ForestMarkedFrameReflection.increments_reflection (tree i x) (reflection i x) (frames i x)
    (compatible i x) _ (input_leaf_reflection i x k) v

theorem markedParameters_mem (k : ℕ) :
    (markedLocalRadii i x k, markedIncrements i x k) ∈
      ForestMarkedFrameReflection.parameterSubmodule (tree i x) (reflection i x) :=
  ⟨markedLocalRadii_reflection i x k, markedIncrements_reflection i x k⟩

/-- The actual limit belongs to the same closed real linear subspace as all
finite-scale marked parameters. -/
theorem limitingParameters_mem :
    (limitingRadii i x, limitingIncrements i x) ∈
      ForestMarkedFrameReflection.parameterSubmodule (tree i x) (reflection i x) :=
  (ForestMarkedFrameReflection.isClosed_parameterSubmodule (tree i x) (reflection i x)).mem_of_tendsto
    (tendsto_markedParameters i x) (Filter.Eventually.of_forall (markedParameters_mem i x))

theorem limitingRadii_reflection (v : tree i x) :
    limitingRadii i x (reflection i x v) = limitingRadii i x v :=
  (limitingParameters_mem i x).1 v

theorem limitingIncrements_reflection (v : tree i x) :
    limitingIncrements i x (reflection i x v) = conj (limitingIncrements i x v) :=
  (limitingParameters_mem i x).2 v

/-- Actual finite parameters bundled in the reflected real parameter space. -/
def reflectedParameters (k : ℕ) :
    ForestMarkedFrameReflection.parameterSubmodule (tree i x) (reflection i x) :=
  ⟨(markedLocalRadii i x k, markedIncrements i x k), markedParameters_mem i x k⟩

def reflectedLimit : ForestMarkedFrameReflection.parameterSubmodule (tree i x) (reflection i x) :=
  ⟨(limitingRadii i x, limitingIncrements i x), limitingParameters_mem i x⟩

theorem tendsto_reflectedParameters :
    Tendsto (reflectedParameters i x) atTop (𝓝 (reflectedLimit i x)) :=
  tendsto_subtype_rng.mpr (tendsto_markedParameters i x)

end EnvelopingIsomorphism.Deformation.Kontsevich.ExtractedMarkedFrameReflection
