import EnvelopingIsomorphism.Deformation.SymmetrizedGraphInsertion
import EnvelopingIsomorphism.FormalSeries.LaurentGroupedMultilinear

/-! Actual Laurent transfer for normalized graph symmetrization and grouped insertion. -/

noncomputable section
set_option maxSynthPendingDepth 3
namespace EnvelopingIsomorphism.Deformation.SymmetrizedGraphLaurent

open scoped BigOperators Classical
open GraphWeightedInsertion SymmetrizedGraphProfiles SymmetrizedGraphInsertion
open EnvelopingIsomorphism.FormalSeries LaurentModule

variable {k : Type*} [Field k] [CharZero k] {a b n d : ℕ}

omit [CharZero k] in
theorem symmetrize_eq_sum (F : ProfileMap k d n) :
    symmetrize F = (n.factorial : k)⁻¹ • ∑ σ : Equiv.Perm (Fin n), F.domDomCongr σ := by
  simp only [symmetrize, LinearMap.smul_apply, LinearMap.sum_apply]
  rfl

/-- Symmetrization disappears on a repeated genuine Laurent input by exponent reindexing.
The input may have any finite lower bound, including a negative one. -/
theorem applyMultilinear_symmetrize_diagonal (F : ProfileMap k d n)
    (ζ : LaurentModule k (Bivector (k := k) (d := d))) :
    applyMultilinear (symmetrize F) (fun _ ↦ ζ) = applyMultilinear F (fun _ ↦ ζ) := by
  rw [symmetrize_eq_sum]
  change applyMultilinearLinear (fun _ : Fin n ↦ ζ)
    ((n.factorial : k)⁻¹ • ∑ σ : Equiv.Perm (Fin n), F.domDomCongr σ) = _
  rw [map_smul, map_sum]
  simp only [applyMultilinearLinear_apply, applyMultilinear_domDomCongr, Function.comp_def,
    Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul k, smul_smul]
  rw [inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)), one_smul]

omit [CharZero k] in
/-- One Laurent input bound controls the complete arity-n convolution. -/
theorem boundedBelow_diagonal (F : ProfileMap k d n)
    (ζ : LaurentModule k (Bivector (k := k) (d := d))) (L : ℤ)
    (hζ : BoundedBelow L ζ) :
    BoundedBelow ((n : ℤ) * L) (applyMultilinear F (fun _ ↦ ζ)) := by
  simpa using boundedBelow_applyMultilinear F (fun _ ↦ ζ)
    (b := fun _ ↦ L) (fun _ ↦ hζ)

omit [CharZero k] in
theorem groupedInsertion_eq_groupedBilinear
    (B : Binary k (MvPolynomial (Fin d) k) →ₗ[k]
      Binary k (MvPolynomial (Fin d) k) →ₗ[k] Ternary k (MvPolynomial (Fin d) k))
    (F : BinaryProfileMap k d a) (G : BinaryProfileMap k d b) :
    groupedInsertion B F G = groupedBilinear B F G := rfl

omit [CharZero k] in
/-- The existing graph grouped insertion commutes with actual Laurent convolution. -/
theorem applyMultilinear_groupedInsertion
    (B : Binary k (MvPolynomial (Fin d) k) →ₗ[k]
      Binary k (MvPolynomial (Fin d) k) →ₗ[k] Ternary k (MvPolynomial (Fin d) k))
    (F : BinaryProfileMap k d a) (G : BinaryProfileMap k d b)
    (x : Fin (a + b) → LaurentModule k (Bivector (k := k) (d := d))) :
    applyMultilinear (groupedInsertion B F G) x = extendBilinear B
      (applyMultilinear F (fun i ↦ x (Fin.castAdd b i)))
      (applyMultilinear G (fun j ↦ x (Fin.natAdd a j))) :=
  applyMultilinear_groupedBilinear B F G x

omit [CharZero k] in
theorem applyMultilinear_groupedInsertion_diagonal
    (B : Binary k (MvPolynomial (Fin d) k) →ₗ[k]
      Binary k (MvPolynomial (Fin d) k) →ₗ[k] Ternary k (MvPolynomial (Fin d) k))
    (F : BinaryProfileMap k d a) (G : BinaryProfileMap k d b)
    (ζ : LaurentModule k (Bivector (k := k) (d := d))) :
    applyMultilinear (groupedInsertion B F G) (fun _ ↦ ζ) = extendBilinear B
      (applyMultilinear F (fun _ ↦ ζ)) (applyMultilinear G (fun _ ↦ ζ)) :=
  applyMultilinear_groupedInsertion B F G _

/-- The requested symmetrized graph insertion transfer on full Laurent inputs. -/
theorem applyMultilinear_symmetrized_groupedInsertion_diagonal
    (B : Binary k (MvPolynomial (Fin d) k) →ₗ[k]
      Binary k (MvPolynomial (Fin d) k) →ₗ[k] Ternary k (MvPolynomial (Fin d) k))
    (F : BinaryProfileMap k d a) (G : BinaryProfileMap k d b)
    (ζ : LaurentModule k (Bivector (k := k) (d := d))) :
    applyMultilinear (symmetrize (groupedInsertion B F G)) (fun _ ↦ ζ) = extendBilinear B
      (applyMultilinear F (fun _ ↦ ζ)) (applyMultilinear G (fun _ ↦ ζ)) := by
  rw [applyMultilinear_symmetrize_diagonal, applyMultilinear_groupedInsertion_diagonal]

omit [CharZero k] in
/-- The two-stage coefficient formula retains both complete inner exponent convolutions. -/
theorem coeff_groupedInsertion_diagonal
    (B : Binary k (MvPolynomial (Fin d) k) →ₗ[k]
      Binary k (MvPolynomial (Fin d) k) →ₗ[k] Ternary k (MvPolynomial (Fin d) k))
    (F : BinaryProfileMap k d a) (G : BinaryProfileMap k d b)
    (ζ : LaurentModule k (Bivector (k := k) (d := d))) (t : ℤ) :
    coeff (applyMultilinear (groupedInsertion B F G) (fun _ ↦ ζ)) t =
      ∑ᶠ e : Fin 2 → ℤ, if ∑ i, e i = t then
        B (convolutionCoeff F (fun _ ↦ ζ) (e 0))
          (convolutionCoeff G (fun _ ↦ ζ) (e 1)) else 0 := by
  rw [applyMultilinear_groupedInsertion_diagonal, coeff_extendBilinear]
  simp only [coeff_applyMultilinear]

end EnvelopingIsomorphism.Deformation.SymmetrizedGraphLaurent
