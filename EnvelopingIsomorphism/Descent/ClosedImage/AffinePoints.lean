import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! # Affine points and their Zariski topology

This type synonym prevents the Zariski topology on affine space from being
confused with a product topology on its coordinates.
-/

namespace EnvelopingIsomorphism.Descent

noncomputable section

open Set Topology MvPolynomial

/-- Affine-space points, with the Zariski topology rather than a product topology. -/
def AffinePoint (k σ : Type*) := σ → k

namespace AffinePoint

variable {k σ τ : Type*} [Field k]

/-- The coordinate tuple of an affine point. -/
def toFunction (x : AffinePoint k σ) : σ → k := x

instance : CoeFun (AffinePoint k σ) (fun _ => σ → k) := ⟨toFunction⟩

/-- Regard a tuple as an affine-space point. -/
def ofFunction (x : σ → k) : AffinePoint k σ := x

/-- The maximal ideal associated to an affine point, viewed in the prime spectrum. -/
def toPrime (x : AffinePoint k σ) : PrimeSpectrum (MvPolynomial σ k) :=
  pointToPoint (k := k) x.toFunction

instance : TopologicalSpace (AffinePoint k σ) :=
  TopologicalSpace.induced toPrime inferInstance

theorem isInducing_toPrime : IsInducing (toPrime : AffinePoint k σ → _) := ⟨rfl⟩

theorem continuous_toPrime : Continuous (toPrime : AffinePoint k σ → _) :=
  isInducing_toPrime.continuous

theorem toPrime_injective : Function.Injective (toPrime : AffinePoint k σ → _) := by
  intro x y h
  apply funext
  intro i
  change x.toFunction i = y.toFunction i
  have hx : X i - C (x.toFunction i) ∈ (toPrime x).asIdeal := by
    change X i - C (x.toFunction i) ∈ vanishingIdeal k {x.toFunction}
    simp
  have hy : X i - C (x.toFunction i) ∈ (toPrime y).asIdeal := by rwa [← h]
  change X i - C (x.toFunction i) ∈ vanishingIdeal k {y.toFunction} at hy
  exact (sub_eq_zero.mp (by simpa using hy)).symm

theorem isEmbedding_toPrime : IsEmbedding (toPrime : AffinePoint k σ → _) :=
  ⟨isInducing_toPrime, toPrime_injective⟩

/-- The zero set of an ideal, as affine-space points. -/
def zeros (I : Ideal (MvPolynomial σ k)) : Set (AffinePoint k σ) :=
  {x | x.toFunction ∈ zeroLocus k I}

theorem zeros_eq_preimage (I : Ideal (MvPolynomial σ k)) :
    zeros I = toPrime ⁻¹' PrimeSpectrum.zeroLocus (I : Set (MvPolynomial σ k)) := by
  ext x
  change (∀ p ∈ I, aeval x.toFunction p = 0) ↔
    ∀ p ∈ I, p ∈ vanishingIdeal k {x.toFunction}
  simp only [mem_vanishingIdeal_singleton_iff]

theorem isClosed_zeros (I : Ideal (MvPolynomial σ k)) : IsClosed (zeros I) := by
  rw [zeros_eq_preimage]
  exact (PrimeSpectrum.isClosed_zeroLocus _).preimage continuous_toPrime

theorem zeros_sup (I J : Ideal (MvPolynomial σ k)) : zeros (I ⊔ J) = zeros I ∩ zeros J := by
  ext x
  change (I ⊔ J ≤ RingHom.ker (aeval x.toFunction).toRingHom) ↔
    (I ≤ RingHom.ker (aeval x.toFunction).toRingHom ∧
      J ≤ RingHom.ker (aeval x.toFunction).toRingHom)
  exact sup_le_iff

/-- Every Zariski closed set of affine points is the zero set of an ideal. -/
theorem isClosed_iff_zeros (s : Set (AffinePoint k σ)) :
    IsClosed s ↔ ∃ I : Ideal (MvPolynomial σ k), s = zeros I := by
  constructor
  · intro hs
    obtain ⟨Z, hZ, hpre⟩ := isClosed_induced_iff.mp hs
    obtain ⟨I, hI⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal Z).mp hZ
    exact ⟨I, hpre.symm.trans (hI ▸ (zeros_eq_preimage I).symm)⟩
  · rintro ⟨I, rfl⟩
    exact isClosed_zeros I

/-- A polynomial map on affine-space points. -/
def polynomialMap (F : τ → MvPolynomial σ k) (x : AffinePoint k σ) : AffinePoint k τ :=
  fun i => aeval x.toFunction (F i)

theorem toPrime_polynomialMap (F : τ → MvPolynomial σ k) (x : AffinePoint k σ) :
    toPrime (polynomialMap F x) = PrimeSpectrum.comap (aeval F).toRingHom (toPrime x) := by
  apply PrimeSpectrum.ext
  ext p
  change p ∈ vanishingIdeal k {(polynomialMap F x).toFunction} ↔
    aeval F p ∈ vanishingIdeal k {x.toFunction}
  rw [mem_vanishingIdeal_singleton_iff, mem_vanishingIdeal_singleton_iff]
  change aeval (fun i => aeval x.toFunction (F i)) p = 0 ↔
    aeval x.toFunction (aeval F p) = 0
  rw [comp_aeval_apply]

theorem continuous_polynomialMap (F : τ → MvPolynomial σ k) :
    Continuous (polynomialMap F) := by
  apply isInducing_toPrime.continuous_iff.mpr
  have heq : toPrime ∘ polynomialMap F =
      PrimeSpectrum.comap (aeval F).toRingHom ∘ toPrime := by
    funext x
    exact toPrime_polynomialMap F x
  rw [heq]
  exact (PrimeSpectrum.continuous_comap _).comp continuous_toPrime

/-- A prime above a rational target point can be enlarged to a maximal ideal,
which gives a rational source point by Nullstellensatz. Thus taking the
algebraic-point image is exactly pulling back the image on prime spectra. -/
theorem polynomialMap_image_zeros_eq_preimage [IsAlgClosed k] [Finite σ]
    (I : Ideal (MvPolynomial σ k)) (F : τ → MvPolynomial σ k) :
    polynomialMap F '' zeros I = toPrime ⁻¹'
      (PrimeSpectrum.comap (aeval F).toRingHom ''
        PrimeSpectrum.zeroLocus (I : Set (MvPolynomial σ k))) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨toPrime x, ?_, (toPrime_polynomialMap F x).symm⟩
    exact (congrArg (fun s => x ∈ s) (zeros_eq_preimage I)).mp hx
  · rintro ⟨P, hPI, hPy⟩
    obtain ⟨M, hM, hPM⟩ := Ideal.exists_le_maximal P.asIdeal P.isPrime.ne_top
    obtain ⟨x, hMx⟩ := eq_vanishingIdeal_singleton_of_isMaximal k hM
    have hPy' : P.asIdeal.comap (aeval F).toRingHom =
        vanishingIdeal k {y.toFunction} := congrArg PrimeSpectrum.asIdeal hPy
    have hmax : (vanishingIdeal k {y.toFunction}).IsMaximal := inferInstance
    have htarget : vanishingIdeal k {y.toFunction} = M.comap (aeval F).toRingHom := by
      apply hmax.eq_of_le (Ideal.comap_ne_top _ hM.ne_top)
      rw [← hPy']
      exact Ideal.comap_mono hPM
    refine ⟨ofFunction x, ?_, ?_⟩
    · intro p hp
      apply (mem_vanishingIdeal_singleton_iff x p).mp
      rw [← hMx]
      exact hPM (hPI hp)
    · apply toPrime_injective
      rw [toPrime_polynomialMap]
      apply PrimeSpectrum.ext
      change (vanishingIdeal k {x}).comap (aeval F).toRingHom =
        vanishingIdeal k {y.toFunction}
      rw [← hMx]
      exact htarget.symm

end AffinePoint

end

end EnvelopingIsomorphism.Descent
