import EnvelopingIsomorphism.Deformation.Kontsevich.ClusterAngularCoordinates
import EnvelopingIsomorphism.Deformation.Kontsevich.ClusterFreeCoordinateEquiv
import Mathlib.Topology.LocalAtTarget

/-!
# Local angular charts on the admissible nonnegative-radius cluster domain

The domain is an open subset of the explicit radial half-space. The standard
local circle cover, combined with the proved free-coordinate homeomorphism,
gives a genuine local homeomorphism to the normalized cluster slice.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich

open Topology Set

/-- Local homeomorphisms restrict to arbitrary target subspaces and their preimages. -/
theorem isLocalHomeomorph_restrictPreimage {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : IsLocalHomeomorph f) (T : Set Y) :
    IsLocalHomeomorph (T.restrictPreimage f) := by
  apply isLocalHomeomorph_iff_isOpenEmbedding_restrict.mpr
  intro x
  obtain ⟨U, hU, he⟩ := isLocalHomeomorph_iff_isOpenEmbedding_restrict.mp hf x.val
  let W : Set (f ⁻¹' T) := {y | y.val ∈ U}
  have hW : W ∈ nhds x := continuous_subtype_val.continuousAt hU
  let e : W ≃ₜ ((U.restrict f) ⁻¹' T) :=
    { toEquiv :=
        { toFun := fun y => ⟨⟨y.val.val, y.property⟩, y.val.property⟩
          invFun := fun y => ⟨⟨y.val.val, y.property⟩, y.val.property⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  refine ⟨W, hW, ?_⟩
  exact (he.restrictPreimage T).comp e.isOpenEmbedding

def ClusterAngularDomain {n : ℕ} (i a b : Fin n) (S : Finset (Fin n)) (m : ℕ) :=
  {x : ClusterAngularCoordinates i a b S m // 0 ≤ x.toFree.radius ∧ x.toFree.OpenConditions}

namespace ClusterAngularDomain

variable {n m : ℕ} {i a b : Fin n} {S : Finset (Fin n)}

instance : TopologicalSpace (ClusterAngularDomain i a b S m) :=
  inferInstanceAs (TopologicalSpace {x : ClusterAngularCoordinates i a b S m //
    0 ≤ x.toFree.radius ∧ x.toFree.OpenConditions})

def toFreeDomain (x : ClusterAngularDomain i a b S m) : ClusterFreeDomain i a b S m :=
  ⟨x.val.toFree, x.property⟩

theorem isLocalHomeomorph_toFreeDomain :
    IsLocalHomeomorph (toFreeDomain : ClusterAngularDomain i a b S m → ClusterFreeDomain i a b S m) :=
  isLocalHomeomorph_restrictPreimage ClusterAngularCoordinates.isLocalHomeomorph_toFree
    {x : ClusterFreeCoordinates i a b S m | 0 ≤ x.radius ∧ x.OpenConditions}

theorem surjective_toFreeDomain :
    Function.Surjective (toFreeDomain : ClusterAngularDomain i a b S m → ClusterFreeDomain i a b S m) := by
  intro x
  obtain ⟨y, hy⟩ := ClusterAngularCoordinates.surjective_toFree x.val
  refine ⟨⟨y, ?_⟩, Subtype.ext hy⟩
  simpa only [hy] using x.property

def toSlice (ha : a ∈ S) (hb : b ∈ S) (hba : b ≠ a) (hanchor : i ∈ S → a = i)
    (x : ClusterAngularDomain i a b S m) : NormalizedInteriorClusterSlice i m S a b :=
  clusterFreeHomeomorph ha hb hba hanchor (toFreeDomain x)

theorem isLocalHomeomorph_toSlice (ha : a ∈ S) (hb : b ∈ S) (hba : b ≠ a)
    (hanchor : i ∈ S → a = i) :
    IsLocalHomeomorph (toSlice ha hb hba hanchor : ClusterAngularDomain i a b S m → _) :=
  (clusterFreeHomeomorph ha hb hba hanchor).isLocalHomeomorph.comp isLocalHomeomorph_toFreeDomain

theorem surjective_toSlice (ha : a ∈ S) (hb : b ∈ S) (hba : b ≠ a)
    (hanchor : i ∈ S → a = i) :
    Function.Surjective (toSlice ha hb hba hanchor : ClusterAngularDomain i a b S m → _) :=
  (clusterFreeHomeomorph ha hb hba hanchor).surjective.comp surjective_toFreeDomain

/-- The ambient half-space has just the radial coordinate constrained to be nonnegative. -/
def HalfSpace (i a b : Fin n) (S : Finset (Fin n)) (m : ℕ) :=
  {x : ClusterAngularCoordinates i a b S m // 0 ≤ x.toFree.radius}

instance : TopologicalSpace (HalfSpace i a b S m) :=
  inferInstanceAs (TopologicalSpace {x : ClusterAngularCoordinates i a b S m // 0 ≤ x.toFree.radius})

theorem isOpen_in_halfSpace :
    IsOpen {x : HalfSpace i a b S m | x.val.toFree.OpenConditions} :=
  ClusterFreeCoordinates.isOpen_openConditions.preimage
    (ClusterAngularCoordinates.continuous_toFree.comp continuous_subtype_val)

/-- The angular admissible domain is exactly an open subset of the radial half-space. -/
def halfSpaceHomeomorph : ClusterAngularDomain i a b S m ≃ₜ
    {x : HalfSpace i a b S m // x.val.toFree.OpenConditions} where
  toFun x := ⟨⟨x.val, x.property.1⟩, x.property.2⟩
  invFun x := ⟨x.val.val, x.val.property, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

end ClusterAngularDomain

end EnvelopingIsomorphism.Deformation.Kontsevich
