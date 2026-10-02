import EnvelopingIsomorphism.FormalSeries.LaurentGroupedMultilinear
import EnvelopingIsomorphism.FormalSeries.MultilinearPartialEvaluation

/-! Fixed-arity power-series convolution for disjoint-group maps over arbitrary coefficient modules. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.FormalSeries.PowerSeriesModule
open scoped BigOperators Classical


section Relabelling
variable {k ι κ V Z : Type*} [CommRing k] [Fintype ι] [Fintype κ]
  [AddCommGroup V] [Module k V] [AddCommGroup Z] [Module k Z]

/-- Relabelling slots reindexes the actual natural-number exponent tuples. -/
theorem applyMultilinear_domDomCongr (e : ι ≃ κ)
    (F : MultilinearMap k (fun _ : ι ↦ V) Z) (x : κ → PowerSeriesModule k V) :
    applyMultilinear (F.domDomCongr e) x = applyMultilinear F (x ∘ e) := by
  apply PowerSeriesModule.ext
  intro d
  simp only [coeffV_applyMultilinear, MultilinearMap.domDomCongr_apply]
  apply Finset.sum_nbij' (fun a ↦ a ∘ e) (fun a ↦ a ∘ e.symm)
  · intro a ha
    apply Finset.mem_piAntidiag.mpr
    refine ⟨?_, by simp⟩
    exact (e.sum_comp a).trans (Finset.mem_piAntidiag.mp ha).1
  · intro a ha
    apply Finset.mem_piAntidiag.mpr
    refine ⟨?_, by simp⟩
    exact (e.symm.sum_comp a).trans (Finset.mem_piAntidiag.mp ha).1
  · intro a ha
    funext i
    simp
  · intro a ha
    funext i
    simp
  · intro a ha
    rfl

/-- Coefficientwise power-series evaluation is linear in the multilinear operation. -/
def applyMultilinearLinear (x : ι → PowerSeriesModule k V) :
    MultilinearMap k (fun _ : ι ↦ V) Z →ₗ[k] PowerSeriesModule k Z where
  toFun F := applyMultilinear F x
  map_add' F G := by
    apply PowerSeriesModule.ext
    intro d
    simp only [coeffV_applyMultilinear, coeffV_add, add_apply, Finset.sum_add_distrib]
  map_smul' c F := by
    apply PowerSeriesModule.ext
    intro d
    simp only [coeffV_applyMultilinear, coeffV_smul, smul_apply, Finset.smul_sum, RingHom.id_apply]

@[simp] theorem applyMultilinearLinear_apply (x : ι → PowerSeriesModule k V)
    (F : MultilinearMap k (fun _ : ι ↦ V) Z) :
    applyMultilinearLinear x F = applyMultilinear F x := rfl
end Relabelling

section Antidiagonal
-- Match the decidable equality used by the actual `applyMultilinear` convolution.
local instance (m : ℕ) : DecidableEq (Fin m) := Classical.decEq _
variable {a b : ℕ} {A : Type*} [AddCommMonoid A]

/-- Split every total exponent tuple into its two disjoint input groups, retaining all terms. -/
theorem sum_piAntidiag_add (h : (Fin (a + b) → ℕ) → A) (n : ℕ) :
    (∑ q ∈ Finset.piAntidiag Finset.univ n, h q) =
      ∑ rs ∈ Finset.HasAntidiagonal.antidiagonal n,
        ∑ u ∈ Finset.piAntidiag Finset.univ rs.1,
          ∑ v ∈ Finset.piAntidiag Finset.univ rs.2, h (Fin.addCases u v) := by
  simp only [Finset.sum_sigma']
  apply Finset.sum_nbij'
    (fun q ↦ ⟨(∑ i, q (Fin.castAdd b i), ∑ j, q (Fin.natAdd a j)),
      (fun i ↦ q (Fin.castAdd b i)), (fun j ↦ q (Fin.natAdd a j))⟩)
    (fun ⟨rs, u, v⟩ ↦ Fin.addCases u v)
  · intro q hq
    simp only [Finset.mem_sigma, Finset.mem_piAntidiag, Finset.mem_univ,
      implies_true, and_true, Finset.HasAntidiagonal.mem_antidiagonal] at hq ⊢
    simpa only [Fin.sum_univ_add] using hq
  · rintro ⟨rs, u, v⟩ hv
    simp only [Finset.mem_sigma, Finset.mem_piAntidiag, Finset.mem_univ,
      implies_true, and_true, Finset.HasAntidiagonal.mem_antidiagonal] at hv ⊢
    simpa only [Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right, hv.2.1, hv.2.2] using hv.1
  · intro q hq
    funext i
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) i <;> simp
  · rintro ⟨⟨r,s⟩,u,v⟩ hv
    simp only [Finset.mem_sigma, Finset.mem_piAntidiag, Finset.mem_univ,
      implies_true, and_true, Finset.HasAntidiagonal.mem_antidiagonal] at hv
    simp only [Fin.addCases_left, Fin.addCases_right, hv.2.1, hv.2.2]
  · intro q hq
    congr 1
    funext i
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) i <;> simp
end Antidiagonal


section Grouped
universe u v
variable {k : Type u} [CommRing k] {V X Y Z : Type v}
  [AddCommGroup V] [Module k V] [AddCommGroup X] [Module k X]
  [AddCommGroup Y] [Module k Y] [AddCommGroup Z] [Module k Z] {a b : ℕ}

/-- The actual finite grouped convolution equals the nested bilinear convolution. -/
theorem applyMultilinear_groupedBilinear (B : X →ₗ[k] Y →ₗ[k] Z)
    (F : MultilinearMap k (fun _ : Fin a ↦ V) X)
    (G : MultilinearMap k (fun _ : Fin b ↦ V) Y)
    (x : Fin (a + b) → PowerSeriesModule k V) :
    applyMultilinear (LaurentModule.groupedBilinear B F G) x = applyBilinear B
      (applyMultilinear F (fun i ↦ x (Fin.castAdd b i)))
      (applyMultilinear G (fun j ↦ x (Fin.natAdd a j))) := by
  apply PowerSeriesModule.ext
  intro n
  simp only [coeffV_applyMultilinear, coeffV_applyBilinear, LaurentModule.groupedBilinear_apply]
  have hs := sum_piAntidiag_add (a := a) (b := b)
    (fun q ↦ B (F (fun i ↦ coeffV (q (Fin.castAdd b i)) (x (Fin.castAdd b i))))
      (G (fun j ↦ coeffV (q (Fin.natAdd a j)) (x (Fin.natAdd a j))))) n
  refine hs.trans ?_
  apply Finset.sum_congr rfl
  intro rs hrs
  simp only [Fin.addCases_left, Fin.addCases_right, map_sum, LinearMap.sum_apply]
  rw [Finset.sum_comm]

theorem applyMultilinear_groupedBilinear_diagonal (B : X →ₗ[k] Y →ₗ[k] Z)
    (F : MultilinearMap k (fun _ : Fin a ↦ V) X)
    (G : MultilinearMap k (fun _ : Fin b ↦ V) Y) (ζ : PowerSeriesModule k V) :
    applyMultilinear (LaurentModule.groupedBilinear B F G) (fun _ ↦ ζ) = applyBilinear B
      (applyMultilinear F (fun _ ↦ ζ)) (applyMultilinear G (fun _ ↦ ζ)) :=
  applyMultilinear_groupedBilinear B F G _

end Grouped


section LaurentCoefficients
universe u v
variable {k : Type u} [CommRing k] {V X Y Z : Type v}
  [AddCommGroup V] [Module k V] [AddCommGroup X] [Module k X]
  [AddCommGroup Y] [Module k Y] [AddCommGroup Z] [Module k Z] {a b : ℕ}

/-- The grouped map extends over the full Laurent scalar ring. -/
theorem extendScalars_groupedBilinear (B : X →ₗ[k] Y →ₗ[k] Z)
    (F : MultilinearMap k (fun _ : Fin a ↦ V) X)
    (G : MultilinearMap k (fun _ : Fin b ↦ V) Y) :
    LaurentModule.extendScalars (LaurentModule.groupedBilinear B F G) =
      LaurentModule.groupedBilinear (LaurentModule.extendBilinear B)
        (LaurentModule.extendScalars F) (LaurentModule.extendScalars G) := by
  apply MultilinearMap.ext
  intro x
  exact LaurentModule.applyMultilinear_groupedBilinear B F G x

/-- Fixed-arity t-adic convolution of the actual bounded Laurent extensions. -/
theorem applyMultilinear_groupedBilinear_laurent (B : X →ₗ[k] Y →ₗ[k] Z)
    (F : MultilinearMap k (fun _ : Fin a ↦ V) X)
    (G : MultilinearMap k (fun _ : Fin b ↦ V) Y)
    (x : Fin (a + b) → PowerSeriesModule (LaurentSeries k) (LaurentModule k V)) :
    applyMultilinear (LaurentModule.extendScalars (LaurentModule.groupedBilinear B F G)) x =
      applyBilinear (LaurentModule.extendBilinear B)
        (applyMultilinear (LaurentModule.extendScalars F) (fun i ↦ x (Fin.castAdd b i)))
        (applyMultilinear (LaurentModule.extendScalars G) (fun j ↦ x (Fin.natAdd a j))) := by
  rw [extendScalars_groupedBilinear, applyMultilinear_groupedBilinear]

theorem applyMultilinear_groupedBilinear_laurent_diagonal (B : X →ₗ[k] Y →ₗ[k] Z)
    (F : MultilinearMap k (fun _ : Fin a ↦ V) X)
    (G : MultilinearMap k (fun _ : Fin b ↦ V) Y)
    (ζ : PowerSeriesModule (LaurentSeries k) (LaurentModule k V)) :
    applyMultilinear (LaurentModule.extendScalars (LaurentModule.groupedBilinear B F G)) (fun _ ↦ ζ) =
      applyBilinear (LaurentModule.extendBilinear B)
        (applyMultilinear (LaurentModule.extendScalars F) (fun _ ↦ ζ))
        (applyMultilinear (LaurentModule.extendScalars G) (fun _ ↦ ζ)) :=
  applyMultilinear_groupedBilinear_laurent B F G _

/-- Selected t-series inputs and fixed Laurent constants agree with actual partial evaluation. -/
theorem applyMultilinear_partialFinset_laurent_diagonal {m n j : ℕ} {s : Finset (Fin m)}
    (hs : s.card = n) (hc : sᶜ.card = j)
    (F : MultilinearMap k (fun _ : Fin m ↦ V) Z)
    (v : LaurentModule k V) (β : PowerSeriesModule (LaurentSeries k) (LaurentModule k V)) :
    applyMultilinear (partialFinset hs hc (LaurentModule.extendScalars F) (fun _ ↦ v)) (fun _ ↦ β) =
      applyMultilinear (LaurentModule.extendScalars F)
        (s.piecewise (fun _ ↦ β) (fun _ ↦ single 0 v)) :=
  applyMultilinear_partialFinset_diagonal hs hc (LaurentModule.extendScalars F) v β


section Coefficients
-- Match the decidable equality used by the actual `applyMultilinear` convolution.
local instance (m : ℕ) : DecidableEq (Fin m) := Classical.decEq _

/-- The t-degree coefficient contains the exact finite natural antidiagonals and genuine
inner Laurent multilinear convolutions. No arity-summability assumption is involved. -/
theorem coeffV_groupedBilinear_laurent (B : X →ₗ[k] Y →ₗ[k] Z)
    (F : MultilinearMap k (fun _ : Fin a ↦ V) X)
    (G : MultilinearMap k (fun _ : Fin b ↦ V) Y)
    (x : Fin (a + b) → PowerSeriesModule (LaurentSeries k) (LaurentModule k V)) (N : ℕ) :
    coeffV N (applyMultilinear
      (LaurentModule.extendScalars (LaurentModule.groupedBilinear B F G)) x) =
      ∑ rs ∈ Finset.HasAntidiagonal.antidiagonal N, LaurentModule.extendBilinear B
        (∑ u ∈ Finset.piAntidiag Finset.univ rs.1,
          LaurentModule.applyMultilinear F (fun i ↦ coeffV (u i) (x (Fin.castAdd b i))))
        (∑ v ∈ Finset.piAntidiag Finset.univ rs.2,
          LaurentModule.applyMultilinear G (fun j ↦ coeffV (v j) (x (Fin.natAdd a j)))) := by
  rw [applyMultilinear_groupedBilinear_laurent, coeffV_applyBilinear]
  simp only [coeffV_applyMultilinear, LaurentModule.extendScalars_apply]

end Coefficients
end LaurentCoefficients

end EnvelopingIsomorphism.FormalSeries.PowerSeriesModule
