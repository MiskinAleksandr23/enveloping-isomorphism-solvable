import EnvelopingIsomorphism.Deformation.Kontsevich.Compactification
import EnvelopingIsomorphism.Deformation.Kontsevich.DirectionRatioInvariant
import EnvelopingIsomorphism.Deformation.Kontsevich.CompactPositionIdentification
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Changing the normalization anchor on the actual compactification

The compact spaces will be identified through their full doubled directions
and triple distance ratios. The general compact projection lemma below uses
compactness and density to identify the range with the required closure.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich

open Topology Set Configuration

namespace AnchorAssembly

variable {K Y D : Type*} [TopologicalSpace K] [CompactSpace K]
  [TopologicalSpace Y] [T2Space Y]

/-- A continuous image of a compact space is the closure of the image of any
dense parametrizing subset. No surjectivity hypothesis on the projection is needed. -/
theorem range_eq_closure_dense (f : K → Y) (hf : Continuous f) (ι : D → K)
    (hι : DenseRange ι) : Set.range f = closure (Set.range (f ∘ ι)) := by
  rw [Set.range_comp, hf.isClosedMap.closure_image_eq_of_continuous hf,
    hι.closure_range, Set.image_univ]

/-- An injective continuous compact projection gives the actual homeomorphism
onto the closure of the projected original configurations. -/
def projectionHomeomorph (f : K → Y) (hf : Continuous f) (hinj : Function.Injective f)
    (ι : D → K) (hι : DenseRange ι) : K ≃ₜ closure (Set.range (f ∘ ι)) :=
  (hf.isClosedEmbedding hinj).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (range_eq_closure_dense f hf ι hι))

@[simp] theorem projectionHomeomorph_coe (f : K → Y) (hf : Continuous f)
    (hinj : Function.Injective f) (ι : D → K) (hι : DenseRange ι) (x : K) :
    ((projectionHomeomorph f hf hinj ι hι x : closure (Set.range (f ∘ ι))) : Y) = f x := rfl

/-- A version with a separately named common closed range, for comparing anchors. -/
def commonRangeHomeomorph (f : K → Y) (hf : Continuous f) (hinj : Function.Injective f)
    (ι : D → K) (hι : DenseRange ι) (s : Set Y)
    (hs : closure (Set.range (f ∘ ι)) = s) : K ≃ₜ s :=
  (projectionHomeomorph f hf hinj ι hι).trans (Homeomorph.setCongr hs)

@[simp] theorem commonRangeHomeomorph_coe (f : K → Y) (hf : Continuous f)
    (hinj : Function.Injective f) (ι : D → K) (hι : DenseRange ι) (s : Set Y)
    (hs : closure (Set.range (f ∘ ι)) = s) (x : K) :
    ((commonRangeHomeomorph f hf hinj ι hι s hs x : s) : Y) = f x := rfl

end AnchorAssembly

variable {n m : ℕ}

/-- The actual full direction/ratio projection on an anchored compactification. -/
def compactProjectDR {i : Fin n} (x : Compactification i m) : DRData n m := projectDR x.val

@[fun_prop] theorem continuous_compactProjectDR (i : Fin n) :
    Continuous (compactProjectDR : Compactification i m → DRData n m) :=
  continuous_projectDR.comp continuous_subtype_val

/-- Every anchor projects onto precisely the same full direction/ratio closure. -/
theorem range_compactProjectDR (i : Fin n) :
    Set.range (compactProjectDR : Compactification i m → DRData n m) = directionRatioSet n m := by
  rw [AnchorAssembly.range_eq_closure_dense _ (continuous_compactProjectDR i)
    (compactificationEmbedding i) (denseRange_compactificationEmbedding i)]
  exact (directionRatioSet_eq_projected i).symm

/-- Projection to the common, anchor-independent direction/ratio space. -/
def toDRSpace (i : Fin n) (x : Compactification i m) : DRSpace n m :=
  ⟨compactProjectDR x, by
    change compactProjectDR x ∈ directionRatioSet n m
    rw [← range_compactProjectDR i]
    exact ⟨x, rfl⟩⟩

@[simp] theorem toDRSpace_val (i : Fin n) (x : Compactification i m) :
    (toDRSpace i x).val = projectDR x.val := rfl

@[fun_prop] theorem continuous_toDRSpace (i : Fin n) :
    Continuous (toDRSpace i : Compactification i m → DRSpace n m) :=
  (continuous_compactProjectDR i).subtype_mk _

theorem surjective_toDRSpace (i : Fin n) : Function.Surjective (toDRSpace i : Compactification i m → DRSpace n m) := by
  intro y
  have hy : y.val ∈ Set.range (compactProjectDR : Compactification i m → DRData n m) := by
    rw [range_compactProjectDR]
    exact y.property
  obtain ⟨x, hx⟩ := hy
  exact ⟨x, Subtype.ext hx⟩

theorem injective_toDRSpace (i : Fin n) :
    Function.Injective (toDRSpace i : Compactification i m → DRSpace n m) := by
  intro x y h
  exact projectDR_injective_on_compactification i (congrArg Subtype.val h)

/-- Every anchored compactification is homeomorphic to the same full
direction/ratio closure. Injectivity is the proved identification of all positions. -/
def toDRHomeomorph (i : Fin n) : Compactification i m ≃ₜ DRSpace n m :=
  (Equiv.ofBijective (toDRSpace i)
    ⟨injective_toDRSpace i, surjective_toDRSpace i⟩).toHomeomorphOfContinuousClosed
      (continuous_toDRSpace i) (continuous_toDRSpace i).isClosedMap

@[simp] theorem toDRHomeomorph_apply (i : Fin n) (x : Compactification i m) :
    toDRHomeomorph i x = toDRSpace i x := rfl

@[simp] theorem toDRHomeomorph_val (i : Fin n) (x : Compactification i m) :
    (toDRHomeomorph i x).val = projectDR x.val := rfl

/-- The actual change of normalization anchor on the entire compactification. -/
def anchorHomeomorph (i j : Fin n) : Compactification i m ≃ₜ Compactification j m :=
  (toDRHomeomorph i).trans (toDRHomeomorph j).symm

/-- Changing the anchor preserves the complete doubled direction and triple
distance ratio data, including at boundary and infinite configurations. -/
@[simp] theorem projectDR_anchorHomeomorph (i j : Fin n) (x : Compactification i m) :
    projectDR (anchorHomeomorph i j x).val = projectDR x.val := by
  exact congrArg Subtype.val ((toDRHomeomorph j).apply_symm_apply (toDRHomeomorph i x))

@[simp] theorem anchorHomeomorph_direction (i j : Fin n) (x : Compactification i m)
    (p : DoubledPair n m) :
    (anchorHomeomorph i j x).val.2.1 p = x.val.2.1 p :=
  congrFun (congrArg Prod.fst (projectDR_anchorHomeomorph i j x)) p

@[simp] theorem anchorHomeomorph_ratio (i j : Fin n) (x : Compactification i m)
    (t : DoubledTriple n m) :
    (anchorHomeomorph i j x).val.2.2 t = x.val.2.2 t :=
  congrFun (congrArg Prod.snd (projectDR_anchorHomeomorph i j x)) t

/-- On ordinary configurations the compactified homeomorphism is exactly
positive affine renormalization at the new anchor. -/
@[simp] theorem anchorHomeomorph_embedding (i j : Fin n) (c : Normalized i m) :
    anchorHomeomorph i j (compactificationEmbedding i c) =
      compactificationEmbedding j (normalized j c.val) := by
  apply projectDR_injective_on_compactification j
  change projectDR (anchorHomeomorph i j (compactificationEmbedding i c)).val =
    projectDR (compactificationEmbedding j (normalized j c.val)).val
  rw [projectDR_anchorHomeomorph]
  change normalizedDirectionRatios c = normalizedDirectionRatios (normalized j c.val)
  rw [normalizedDirectionRatios_normalized]
  rfl

@[simp] theorem anchorHomeomorph_refl (i : Fin n) :
    anchorHomeomorph (m := m) i i = Homeomorph.refl _ := by
  apply Homeomorph.ext
  intro x
  exact (toDRHomeomorph i).symm_apply_apply x

@[simp] theorem anchorHomeomorph_trans (i j k : Fin n) :
    (anchorHomeomorph (m := m) i j).trans (anchorHomeomorph j k) =
      anchorHomeomorph i k := by
  apply Homeomorph.ext
  intro x
  apply projectDR_injective_on_compactification k
  change projectDR (anchorHomeomorph j k (anchorHomeomorph i j x)).val =
    projectDR (anchorHomeomorph i k x).val
  simp only [projectDR_anchorHomeomorph]

@[simp] theorem anchorHomeomorph_symm (i j : Fin n) :
    (anchorHomeomorph (m := m) i j).symm = anchorHomeomorph j i := by
  rfl

/-- The harmonic phase built from any two doubled directions is unchanged. -/
@[simp] theorem anchorHomeomorph_harmonicPhase (i j a : Fin n)
    (v : Fin n ⊕ Fin m) (hv : v ≠ Sum.inl a) (x : Compactification i m) :
    extendedHarmonicPhase a v hv (anchorHomeomorph i j x) =
      extendedHarmonicPhase a v hv x := by
  simp only [extendedHarmonicPhase, anchorHomeomorph_direction]

end EnvelopingIsomorphism.Deformation.Kontsevich
