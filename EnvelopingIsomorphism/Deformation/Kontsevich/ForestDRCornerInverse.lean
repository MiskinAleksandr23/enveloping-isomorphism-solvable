import EnvelopingIsomorphism.Deformation.Kontsevich.ForestDRInverse
import EnvelopingIsomorphism.Deformation.Kontsevich.ForestParameterSpace

/-! The raw DR corner left inverse, proved by positive reflected density and
continuity. No compactification landing or chart open-image theorem is assumed. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.ForestDRCornerInverse

open ForestMarkedFrames ForestDirectionRatioCoordinates ForestDRInverse
open ForestInsertionDifference ForestParameterSpace ReflectedRadiusOrthant
open Set Filter Topology ComplexConjugate
open scoped Classical

variable (T : RootedTree) [Fintype T] (σ : T ≃o T) (F : Frames T)
variable {I : Type*} [Fintype I] (leaf : I → T)

/-- Positive normalized reflected parameters are dense inside the actual
regular-unit encoder domain, not merely in an unconstrained ambient space. -/
theorem mem_closure_positive (hF : StableFixed T σ F) (x : Domain T leaf)
    (hx : Constraints T σ F x.val) :
    x ∈ closure {y : Domain T leaf | Constraints T σ F y.val ∧ ∀ v, 0 < y.val.1 v} := by
  rw [mem_closure_iff]
  intro U hU hxU
  obtain ⟨V, hV, rfl⟩ := isOpen_induced_iff.mp hU
  have hreg := isOpen_regularUnits T leaf
  obtain ⟨s, hs, hn, hsV⟩ := exists_positive_normalized_in_open T σ F hF
    x.val.1 x.val.2 hx.1 hx.2.2.1 hx.2.1
    (V ∩ {y | RegularUnits T leaf y}) (hV.inter hreg) ⟨hxU, x.property.2⟩
  let y : Domain T leaf := ⟨(s, x.val.2), hs.1.2.2.2, hsV.2⟩
  exact ⟨y, hsV.1, ⟨hs.1, hn, hx.2.2.1, hx.2.2.2⟩, hs.2⟩

variable (lab : T → I) (τ : I → I) (d : References T (I := I))

omit [Fintype I] in
theorem inserted_reflection (hleaf : ∀ i, leaf (τ i) = σ (leaf i))
    (x : Domain T leaf) (hx : Constraints T σ F x.val) (i : I) :
    position T x.val.1 x.val.2 (leaf (τ i)) =
      star (position T x.val.1 x.val.2 (leaf i)) := by
  rw [hleaf i]
  exact ReflectedForestInsertion.position_reflect T σ x.val.1 hx.1.2.2.1
    x.val.2 hx.2.2.1 (leaf i)

/-- Literal decoder left inverse at all nonnegative normalized reflected
corners where the actual resolved data lie in the explicit decoder region. -/
theorem decode_resolved (hF : StableFixed T σ F) (hd : ReferenceModes T F d τ)
    (hlabel : ∀ v, IsMax v → leaf (lab v) = v)
    (hleaf : ∀ i, leaf (τ i) = σ (leaf i))
    (x : Domain T leaf) (hx : Constraints T σ F x.val)
    (hregion : resolvedCoordinates T leaf x ∈ ForestDRInverse.Region T lab F d) :
    decode T lab F d (resolvedCoordinates T leaf x) = x.val := by
  let S : Set (Domain T leaf) :=
    {y | Constraints T σ F y.val ∧ ∀ v, 0 < y.val.1 v}
  have hclosure : x ∈ closure S := mem_closure_positive T σ F leaf hF x hx
  haveI : NeBot (𝓝[S] x) := mem_closure_iff_nhdsWithin_neBot.mp hclosure
  have hcont : ContinuousAt (fun y : Domain T leaf => decode T lab F d (resolvedCoordinates T leaf y)) x :=
    (continuousAt_decode T lab F d _ hregion).comp (continuous_resolvedCoordinates T leaf).continuousAt
  have heq : ∀ᶠ y in 𝓝[S] x,
      decode T lab F d (resolvedCoordinates T leaf y) = y.val := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact decode_resolved_reflected T lab leaf F d τ hd hlabel y hy.2 hy.1.2.1
      hy.1.1.1 hy.1.2.2.2 hy.1.1.2.1 (inserted_reflection T σ F leaf τ hleaf y hy.1)
  exact tendsto_nhds_unique hcont.continuousWithinAt.tendsto
    (continuous_subtype_val.continuousWithinAt.tendsto.congr' (heq.mono fun _ h => h.symm))

/-- The actual constrained regular corner domain restricted to the decoder
region; it uses root's genuine closed parameter equations. -/
abbrev Corner := {x : Domain T leaf // Constraints T σ F x.val ∧
  resolvedCoordinates T leaf x ∈ ForestDRInverse.Region T lab F d}

def encode (x : Corner T σ F leaf lab d) : Data I := resolvedCoordinates T leaf x.val

omit [Fintype I] in
theorem continuous_encode : Continuous (encode T σ F leaf lab d) :=
  (continuous_resolvedCoordinates T leaf).comp continuous_subtype_val

theorem decode_encode (hF : StableFixed T σ F) (hd : ReferenceModes T F d τ)
    (hlabel : ∀ v, IsMax v → leaf (lab v) = v)
    (hleaf : ∀ i, leaf (τ i) = σ (leaf i)) (x : Corner T σ F leaf lab d) :
    decode T lab F d (encode T σ F leaf lab d x) = x.val.val :=
  decode_resolved T σ F leaf lab τ d hF hd hlabel hleaf x.val x.property.1 x.property.2

theorem encode_injective (hF : StableFixed T σ F) (hd : ReferenceModes T F d τ)
    (hlabel : ∀ v, IsMax v → leaf (lab v) = v)
    (hleaf : ∀ i, leaf (τ i) = σ (leaf i)) :
    Function.Injective (encode T σ F leaf lab d) := by
  intro x y hxy
  apply Subtype.ext
  apply Subtype.ext
  rw [← decode_encode T σ F leaf lab τ d hF hd hlabel hleaf x,
    ← decode_encode T σ F leaf lab τ d hF hd hlabel hleaf y, hxy]

/-- The decoder is continuous into ambient parameters; its composition with
the encoder is the actual embedding of the parameter subtype into that ambient
space. This proves a local embedding without asserting any open image. -/
theorem isEmbedding_encode (hF : StableFixed T σ F) (hd : ReferenceModes T F d τ)
    (hlabel : ∀ v, IsMax v → leaf (lab v) = v)
    (hleaf : ∀ i, leaf (τ i) = σ (leaf i)) :
    IsEmbedding (encode T σ F leaf lab d) := by
  let enc : Corner T σ F leaf lab d → ForestDRInverse.Region T lab F d :=
    fun x => ⟨encode T σ F leaf lab d x, x.property.2⟩
  have hc : Continuous enc := (continuous_encode T σ F leaf lab d).subtype_mk _
  have hcomp : IsEmbedding ((fun x : ForestDRInverse.Region T lab F d => decode T lab F d x.val) ∘ enc) := by
    have heq : ((fun x : ForestDRInverse.Region T lab F d => decode T lab F d x.val) ∘ enc) =
        (fun x : Corner T σ F leaf lab d => x.val.val) := by
      funext x
      exact decode_encode T σ F leaf lab τ d hF hd hlabel hleaf x
    rw [heq]
    exact IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal
  have he : IsEmbedding enc := IsEmbedding.of_comp hc (continuous_decode T lab F d) hcomp
  exact IsEmbedding.subtypeVal.comp he

end EnvelopingIsomorphism.Deformation.Kontsevich.ForestDRCornerInverse
