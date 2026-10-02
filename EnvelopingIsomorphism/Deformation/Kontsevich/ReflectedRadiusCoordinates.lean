import EnvelopingIsomorphism.Deformation.Kontsevich.ForestParameterProduct
import Mathlib.Topology.Instances.NNReal.Lemmas

/-! Genuine free radius coordinates: one nonnegative coordinate for each reflection
orbit of internal nonroot nodes, with root and leaf radii fixed to one. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich.ReflectedRadiusCoordinates

open scoped Classical Topology NNReal

variable (T : RootedTree) (σ : T ≃o T)

/-- Exactly the nodes whose radius is a free parameter. -/
def Active (u : T) : Prop := u ≠ ⊥ ∧ ¬ IsMax u

abbrev ActiveNode := {u : T // Active T u}

theorem active_reflect_iff (u : T) : Active T (σ u) ↔ Active T u := by
  have hroot : σ u = ⊥ ↔ u = ⊥ := by
    constructor
    · intro h
      apply σ.injective
      simpa only [σ.map_bot] using h
    · rintro rfl
      exact σ.map_bot
  simp only [Active, ne_eq, hroot, σ.isMax_apply]

/-- Reflection restricted to the actual free nodes, preserving the native tree order. -/
def reflect (u : ActiveNode T) : ActiveNode T :=
  ⟨σ u.val, (active_reflect_iff T σ u.val).mpr u.property⟩

theorem reflect_involutive (hσ : Function.Involutive σ) : Function.Involutive (reflect T σ) := by
  intro u
  exact Subtype.ext (hσ u.val)

/-- A reflection orbit has either one node or the node and its reflection. -/
def orbitSetoid (hσ : Function.Involutive σ) : Setoid (ActiveNode T) where
  r u v := u = v ∨ reflect T σ u = v
  iseqv :=
    { refl := fun _ => Or.inl rfl
      symm := by
        intro u v huv
        rcases huv with rfl | huv
        · exact Or.inl rfl
        · exact Or.inr (by rw [← huv]; exact reflect_involutive T σ hσ u)
      trans := by
        intro u v w huv hvw
        rcases huv with rfl | huv
        · exact hvw
        rcases hvw with rfl | hvw
        · exact Or.inr huv
        · exact Or.inl ((reflect_involutive T σ hσ u).symm.trans (by rw [huv, hvw])) }

abbrev Orbit (hσ : Function.Involutive σ) := Quotient (orbitSetoid T σ hσ)

/-- The actual orbit of a free node. -/
def orbitClass (hσ : Function.Involutive σ) (u : ActiveNode T) : Orbit T σ hσ := Quotient.mk (orbitSetoid T σ hσ) u

theorem orbitClass_reflect (hσ : Function.Involutive σ) (u : ActiveNode T) :
    orbitClass T σ hσ (reflect T σ u) = orbitClass T σ hσ u :=
  (Quotient.sound (show (orbitSetoid T σ hσ).r u (reflect T σ u) from Or.inr rfl)).symm

/-- Actual radius evaluation descends because reflected node radii are equal. -/
def coordinates (hσ : Function.Involutive σ) (r : ForestParameterProduct.RadiusSpace T σ) :
    Orbit T σ hσ → ℝ≥0 :=
  Quotient.lift (fun u : ActiveNode T => (⟨r.val u.val, r.property.2.2.2 u.val⟩ : ℝ≥0)) (by
    intro u v huv
    apply Subtype.ext
    rcases huv with rfl | huv
    · rfl
    · rw [← huv]
      exact (r.property.2.2.1 u.val).symm)

@[simp] theorem coordinates_orbitClass (hσ : Function.Involutive σ)
    (r : ForestParameterProduct.RadiusSpace T σ) (u : ActiveNode T) :
    (coordinates T σ hσ r (orbitClass T σ hσ u) : ℝ) = r.val u.val := rfl

/-- Reconstruct all native radii; root and leaf coordinates are exactly one. -/
def radius (hσ : Function.Involutive σ) (c : Orbit T σ hσ → ℝ≥0) (u : T) : ℝ :=
  if hu : Active T u then c (orbitClass T σ hσ ⟨u, hu⟩) else 1

theorem radius_admissible (hσ : Function.Involutive σ) (c : Orbit T σ hσ → ℝ≥0) :
    ReflectedRadiusOrthant.Admissible T σ (radius T σ hσ c) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [radius, Active]
  · intro u hu
    simp [radius, Active, hu]
  · intro u
    by_cases hu : Active T u
    · have hsu := (active_reflect_iff T σ u).mpr hu
      rw [radius, dif_pos hsu, radius, dif_pos hu]
      exact congrArg (fun o => (c o : ℝ)) (orbitClass_reflect T σ hσ ⟨u, hu⟩)
    · have hsu : ¬ Active T (σ u) := fun h => hu ((active_reflect_iff T σ u).mp h)
      simp only [radius, dif_neg hu, dif_neg hsu]
  · intro u
    by_cases hu : Active T u
    · rw [radius, dif_pos hu]
      exact NNReal.coe_nonneg _
    · simp only [radius, dif_neg hu, zero_le_one]

/-- The inverse coordinate map takes values in the original reflected radius space. -/
def ofCoordinates (hσ : Function.Involutive σ) (c : Orbit T σ hσ → ℝ≥0) :
    ForestParameterProduct.RadiusSpace T σ := ⟨radius T σ hσ c, radius_admissible T σ hσ c⟩

theorem ofCoordinates_coordinates (hσ : Function.Involutive σ)
    (r : ForestParameterProduct.RadiusSpace T σ) : ofCoordinates T σ hσ (coordinates T σ hσ r) = r := by
  apply Subtype.ext
  funext u
  by_cases hu : Active T u
  · simp only [ofCoordinates, radius, dif_pos hu, coordinates_orbitClass]
  · have hfixed : r.val u = 1 := by
      by_cases hroot : u = ⊥
      · subst u
        exact r.property.1
      · exact r.property.2.1 u (not_not.mp (fun hmax => hu ⟨hroot, hmax⟩))
    simp only [ofCoordinates, radius, dif_neg hu, hfixed]

theorem coordinates_ofCoordinates (hσ : Function.Involutive σ) (c : Orbit T σ hσ → ℝ≥0) :
    coordinates T σ hσ (ofCoordinates T σ hσ c) = c := by
  funext o
  induction o using Quotient.inductionOn with
  | h u =>
      apply Subtype.ext
      change radius T σ hσ c u.val = (c (orbitClass T σ hσ u) : ℝ)
      simp only [radius, dif_pos u.property]

/-- Each free coordinate is continuous evaluation at any representative of its orbit. -/
theorem continuous_coordinates (hσ : Function.Involutive σ) : Continuous (coordinates T σ hσ) := by
  apply continuous_pi
  intro o
  induction o using Quotient.inductionOn with
  | h u =>
      change Continuous (fun r : ForestParameterProduct.RadiusSpace T σ =>
        (⟨r.val u.val, r.property.2.2.2 u.val⟩ : ℝ≥0))
      apply Continuous.subtype_mk
      exact (continuous_apply u.val).comp continuous_subtype_val

/-- Reconstructing a native radius is a fixed coordinate evaluation or the constant one. -/
theorem continuous_ofCoordinates (hσ : Function.Involutive σ) : Continuous (ofCoordinates T σ hσ) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro u
  by_cases hu : Active T u
  · simp only [radius, dif_pos hu]
    fun_prop
  · simp only [radius, dif_neg hu]
    exact continuous_const

/-- Actual free reflected radius parameters, with no redundant root or leaf coordinates. -/
def coordinatesHomeomorph (hσ : Function.Involutive σ) :
    ForestParameterProduct.RadiusSpace T σ ≃ₜ (Orbit T σ hσ → ℝ≥0) where
  toEquiv :=
    { toFun := coordinates T σ hσ
      invFun := ofCoordinates T σ hσ
      left_inv := ofCoordinates_coordinates T σ hσ
      right_inv := coordinates_ofCoordinates T σ hσ }
  continuous_toFun := continuous_coordinates T σ hσ
  continuous_invFun := continuous_ofCoordinates T σ hσ

/-- Equality of free coordinates is exactly the native two-point orbit relation. -/
theorem orbitClass_eq_iff (hσ : Function.Involutive σ) (u v : ActiveNode T) :
    orbitClass T σ hσ u = orbitClass T σ hσ v ↔ u = v ∨ reflect T σ u = v :=
  Quotient.eq

variable [Fintype T]

instance orbitFintype (hσ : Function.Involutive σ) : Fintype (Orbit T σ hσ) := Fintype.ofFinite _

/-- The free radius dimension is the actual finite number of internal nonroot reflection orbits. -/
def freeRadiusCount (hσ : Function.Involutive σ) : ℕ := Fintype.card (Orbit T σ hσ)

theorem freeRadiusCount_le_active (hσ : Function.Involutive σ) :
    freeRadiusCount T σ hσ ≤ Fintype.card (ActiveNode T) := by
  apply Fintype.card_le_of_surjective (orbitClass T σ hσ)
  intro o
  induction o using Quotient.inductionOn with
  | h u => exact ⟨u, rfl⟩

/-- Standard finite indexing of the same actual nonnegative free-radius product. -/
def finCoordinatesHomeomorph (hσ : Function.Involutive σ) :
    ForestParameterProduct.RadiusSpace T σ ≃ₜ (Fin (freeRadiusCount T σ hσ) → ℝ≥0) :=
  (coordinatesHomeomorph T σ hσ).trans
    (Homeomorph.piCongrLeft (Y := fun _ : Fin (freeRadiusCount T σ hσ) => ℝ≥0)
      (Fintype.equivFin (Orbit T σ hσ)))

/-- With no active nodes, the free-radius dimension is zero; the coordinate model
still applies and introduces no artificial leaf parameters. -/
theorem freeRadiusCount_eq_zero_of_no_active (hσ : Function.Involutive σ)
    (hactive : ∀ u : T, u = ⊥ ∨ IsMax u) : freeRadiusCount T σ hσ = 0 := by
  haveI : IsEmpty (ActiveNode T) := ⟨fun u => by
    rcases hactive u.val with hu | hu
    · exact u.property.1 hu
    · exact u.property.2 hu⟩
  exact Nat.eq_zero_of_le_zero (by simpa using freeRadiusCount_le_active T σ hσ)

end EnvelopingIsomorphism.Deformation.Kontsevich.ReflectedRadiusCoordinates
