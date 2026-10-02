import EnvelopingIsomorphism.Descent.ClosedImage.FilteredIsomorphismImage
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.MvPolynomial.Tower

/-! Specialization at zero of a regular graded arc. Only its generic point
is compared with the original filtered Lie isomorphism; no series is evaluated at one. -/

namespace EnvelopingIsomorphism.Descent

open MvPolynomial

noncomputable section

universe u v w z

section Specialization

variable {k : Type u} [Field k] {R : Type v} [CommRing R] [Algebra k R]
variable {E : Type w} [Field E] [Algebra k E]
variable {K : Type z} [Field K] [Algebra k K]
variable {ι : Type*}

/-- Polynomial equations descend through an injective generic inclusion and then
specialize along an algebra map. The specified special point is defined over the base field. -/
theorem zeroLocus_of_regular_specialization
    (inclusion : R →ₐ[k] K) (hinjective : Function.Injective inclusion)
    (specialization : R →ₐ[k] E)
    (J : Ideal (MvPolynomial ι k)) (arc : ι → R) (point : ι → k)
    (hgeneric : (fun i => inclusion (arc i)) ∈ zeroLocus K J)
    (hspecial : ∀ i, specialization (arc i) = algebraMap k E (point i)) :
    point ∈ zeroLocus k J := by
  intro q hq
  have hR : aeval arc q = 0 := by
    apply hinjective
    rw [map_zero, comp_aeval_apply]
    exact hgeneric q hq
  have hE : aeval (fun i => specialization (arc i)) q = 0 := by
    rw [← comp_aeval_apply, hR, map_zero]
  have hp : (fun i => specialization (arc i)) = algebraMap k E ∘ point :=
    funext hspecial
  rw [hp, aeval_algebraMap_apply] at hE
  exact (FaithfulSMul.algebraMap_injective k E) (by simpa using hE)

end Specialization

section PowerSeries

variable {k E : Type*} [Field k] [Field E] [Algebra k E]

/-- Constant coefficient as a map over the original coefficient field. -/
def powerSeriesSpecialization : PowerSeries E →ₐ[k] E where
  __ := PowerSeries.constantCoeff
  commutes' a := by simp [PowerSeries.algebraMap_apply]

/-- The canonical inclusion of a regular arc into the Laurent field, over `k`. -/
def powerSeriesGenericInclusion : PowerSeries E →ₐ[k] LaurentSeries E where
  __ := algebraMap (PowerSeries E) (LaurentSeries E)
  commutes' a := by
    simp [PowerSeries.algebraMap_apply, LaurentSeries.coe_algebraMap,
      HahnSeries.algebraMap_apply']

theorem powerSeriesGenericInclusion_injective :
    Function.Injective (powerSeriesGenericInclusion (k := k) (E := E)) :=
  HahnSeries.ofPowerSeries_injective

/-- Specialize the regular `t`-arc, even when its coefficient field itself is a Laurent field. -/
theorem zeroLocus_of_powerSeries_arc {ι : Type*}
    (J : Ideal (MvPolynomial ι k)) (arc : ι → PowerSeries E) (point : ι → k)
    (hgeneric : (fun i => algebraMap (PowerSeries E) (LaurentSeries E) (arc i)) ∈
      zeroLocus (LaurentSeries E) J)
    (hspecial : ∀ i, PowerSeries.constantCoeff (arc i) = algebraMap k E (point i)) :
    point ∈ zeroLocus k J := by
  apply zeroLocus_of_regular_specialization
    (powerSeriesGenericInclusion (k := k) (E := E))
    (powerSeriesGenericInclusion_injective (k := k) (E := E))
    (powerSeriesSpecialization (k := k) (E := E)) J arc point
  · exact hgeneric
  · exact hspecial

end PowerSeries

namespace MatrixGroup

noncomputable section

variable {k E n α : Type*} [Field k] [IsAlgClosed k] [Field E] [Algebra k E]
variable [Fintype n] [DecidableEq n] [LinearOrder α]

/-- H4: a filtered generic isomorphism and a regular graded arc with prescribed
special point yield an actual base-field filtered isomorphism with that diagonal.
The closed-image ideal is produced by H3 rather than assumed. -/
theorem marked_isomorphism_of_regular_graded_arc
    (B C : (n → k) →ₗ[k] (n → k) →ₗ[k] (n → k)) (b : n → α)
    (generic : Coordinate n → LaurentSeries E)
    (hgeneric : generic ∈ zeroLocus (LaurentSeries E) (filteredIsomorphismEquations B C b))
    (arc : Coordinate n → PowerSeries E) (mark : Matrix.GeneralLinearGroup n k)
    (harc : ∀ i, algebraMap (PowerSeries E) (LaurentSeries E) (arc i) =
      aeval generic (diagonalPolynomial (k := k) b i))
    (hmark : ∀ i, PowerSeries.constantCoeff (arc i) = algebraMap k E (coordinates mark i)) :
    ∃ f : blockTriangularSubgroup (k := k) b,
      PreservesBilinear B C f.val ∧ diagonalHom b f = mark := by
  obtain ⟨J, hJ, hcontainment⟩ :=
    filteredIsomorphism_closed_image_of_extension_point B C b generic hgeneric
  have hzero : (coordinates mark).toFunction ∈ zeroLocus k J := by
    apply zeroLocus_of_powerSeries_arc J arc (coordinates mark).toFunction
    · have h := hcontainment generic hgeneric
      have heq : (fun i => algebraMap (PowerSeries E) (LaurentSeries E) (arc i)) =
          fun i => aeval generic (diagonalPolynomial (k := k) b i) := funext harc
      rwa [heq]
    · exact hmark
  have hm : coordinates mark ∈ AffinePoint.zeros J := hzero
  rw [← hJ] at hm
  obtain ⟨g, ⟨f, hf, rfl⟩, heq⟩ := hm
  exact ⟨f, hf, coordinates_injective heq⟩

end

end MatrixGroup

end

end EnvelopingIsomorphism.Descent
