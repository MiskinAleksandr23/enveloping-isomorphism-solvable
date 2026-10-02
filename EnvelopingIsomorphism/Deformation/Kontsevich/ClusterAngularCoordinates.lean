import EnvelopingIsomorphism.Deformation.Kontsevich.ClusterFreeCoordinates
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.Orientation

/-!
# Smooth real-angle coordinates for a normalized cluster

Replace the single circle coordinate by its standard local real-angle cover.
All base and velocity coordinates are smooth functions of this finite-dimensional
real parameter space. The coordinate basis uses `(1,I)` for each complex entry,
followed by boundary, angle, and radial coordinates.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich

open Topology

abbrev ClusterAngularCoordinates {n : ℕ} (i a b : Fin n) (S : Finset (Fin n)) (m : ℕ) :=
  (ClusterCoarseIndex i a S → ℂ) × (ClusterShapeIndex a b S → ℂ) ×
    (Fin m → ℝ) × ℝ × ℝ

namespace ClusterAngularCoordinates

variable {n m : ℕ} {i a b : Fin n} {S : Finset (Fin n)}

def toFree (x : ClusterAngularCoordinates i a b S m) : ClusterFreeCoordinates i a b S m :=
  (x.1, x.2.1, x.2.2.1, Circle.exp x.2.2.2.1, x.2.2.2.2)

@[fun_prop] theorem continuous_toFree :
    Continuous (toFree : ClusterAngularCoordinates i a b S m → _) := by
  unfold toFree
  fun_prop

/-- Standard local angular charts, leaving every other free coordinate fixed. -/
theorem isLocalHomeomorph_toFree :
    IsLocalHomeomorph (toFree : ClusterAngularCoordinates i a b S m → ClusterFreeCoordinates i a b S m) := by
  intro x
  obtain ⟨e, hx, he⟩ := isLocalHomeomorph_circleExp x.2.2.2.1
  let E := (OpenPartialHomeomorph.refl (ClusterCoarseIndex i a S → ℂ)).prod
    ((OpenPartialHomeomorph.refl (ClusterShapeIndex a b S → ℂ)).prod
      ((OpenPartialHomeomorph.refl (Fin m → ℝ)).prod (e.prod (OpenPartialHomeomorph.refl ℝ))))
  refine ⟨E, ?_, ?_⟩
  · simpa [E, OpenPartialHomeomorph.prod_source] using hx
  · funext y
    change (y.1, y.2.1, y.2.2.1, Circle.exp y.2.2.2.1, y.2.2.2.2) =
      (y.1, y.2.1, y.2.2.1, e y.2.2.2.1, y.2.2.2.2)
    rw [he]

theorem surjective_toFree :
    Function.Surjective (toFree : ClusterAngularCoordinates i a b S m → ClusterFreeCoordinates i a b S m) := by
  intro y
  obtain ⟨θ, hθ⟩ := Circle.exp_surjective y.2.2.2.1
  exact ⟨(y.1, y.2.1, y.2.2.1, θ, y.2.2.2.2), by simp [toFree, hθ]⟩

@[fun_prop] theorem contDiff_base (j : Fin n) :
    ContDiff ℝ ⊤ (fun x : ClusterAngularCoordinates i a b S m => x.toFree.base j) := by
  unfold ClusterFreeCoordinates.base toFree
  split_ifs <;> fun_prop

@[fun_prop] theorem contDiff_velocity (j : Fin n) :
    ContDiff ℝ ⊤ (fun x : ClusterAngularCoordinates i a b S m => x.toFree.velocity j) := by
  unfold ClusterFreeCoordinates.velocity toFree
  split_ifs
  · exact contDiff_const
  · have h := contDiff_circleParameter.comp
      (show ContDiff ℝ ⊤ (fun x : ClusterAngularCoordinates i a b S m => x.2.2.2.1) by fun_prop)
    simpa only [Function.comp_def, circleParameter_eq] using h
  · fun_prop
  · exact contDiff_const

@[fun_prop] theorem contDiff_radius :
    ContDiff ℝ ⊤ (fun x : ClusterAngularCoordinates i a b S m => x.toFree.radius) := by
  unfold toFree ClusterFreeCoordinates.radius
  fun_prop

@[fun_prop] theorem contDiff_position (j : Fin n) :
    ContDiff ℝ ⊤ (fun x : ClusterAngularCoordinates i a b S m =>
      x.toFree.base j + (x.toFree.radius : ℂ) * x.toFree.velocity j) :=
  (contDiff_base j).add ((Complex.ofRealCLM.contDiff.comp contDiff_radius).mul (contDiff_velocity j))

/-- The full real dimension of the ambient angular and radial coordinates. -/
theorem finrank_eq (ha : a ∈ S) (hb : b ∈ S) (hba : b ≠ a) (hanchor : i ∈ S → a = i) :
    Module.finrank ℝ (ClusterAngularCoordinates i a b S m) = 2 * n + m - 2 := by
  have hsle : S.card ≤ n := by simpa using Finset.card_le_card (Finset.subset_univ S)
  have hsge : 2 ≤ S.card := by
    have hpair : ({a, b} : Finset (Fin n)) ⊆ S := by
      intro j hj
      rcases Finset.mem_insert.mp hj with h | h
      · simpa only [h] using ha
      · simpa only [Finset.mem_singleton.mp h] using hb
    have h := Finset.card_le_card hpair
    simpa [Finset.card_pair (Ne.symm hba)] using h
  simp only [ClusterAngularCoordinates, Module.finrank_prod, Module.finrank_pi_fintype,
    Complex.finrank_real_complex, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    Module.finrank_self, Fintype.card_fin, card_clusterCoarseIndex i a S ha hanchor,
    card_clusterShapeIndex a b S ha hb hba]
  omega

abbrev CoordinateIndex (i a b : Fin n) (S : Finset (Fin n)) (m : ℕ) :=
  (Σ _ : ClusterCoarseIndex i a S, Fin 2) ⊕ (Σ _ : ClusterShapeIndex a b S, Fin 2) ⊕
    Fin m ⊕ Unit ⊕ Unit

/-- Canonical product basis: real/imaginary pairs, real boundaries, angle, then radius. -/
def coordinateBasis : Module.Basis (CoordinateIndex i a b S m) ℝ (ClusterAngularCoordinates i a b S m) :=
  (Pi.basis (fun _ : ClusterCoarseIndex i a S => Complex.basisOneI)).prod
    ((Pi.basis (fun _ : ClusterShapeIndex a b S => Complex.basisOneI)).prod
      ((Pi.basisFun ℝ (Fin m)).prod
        ((Module.Basis.singleton Unit ℝ).prod (Module.Basis.singleton Unit ℝ))))

/-- The orientation fixed by the explicit product coordinate basis. -/
def coordinateOrientation : Orientation ℝ (ClusterAngularCoordinates i a b S m) (CoordinateIndex i a b S m) := by
  classical
  exact coordinateBasis.orientation

end ClusterAngularCoordinates

end EnvelopingIsomorphism.Deformation.Kontsevich
