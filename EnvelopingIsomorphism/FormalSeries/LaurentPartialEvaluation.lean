import EnvelopingIsomorphism.FormalSeries.MultilinearPartialEvaluation
import EnvelopingIsomorphism.FormalSeries.LaurentBinaryComposition

/-! Actual Laurent completion commutes with partial evaluation, including independent monomial shifts in fixed slots. -/

noncomputable section

namespace EnvelopingIsomorphism.FormalSeries.LaurentModule

open scoped BigOperators Classical

universe u v
variable {k : Type u} [CommRing k] {V W : Type v}
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

/-- Fixing constant inputs commutes with the genuine Laurent extension. Both
multilinear maps are compared on all monomials with their actual uniform bounds. -/
theorem extend_partialEquiv {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (e : α ⊕ β ≃ γ) (f : MultilinearMap k (fun _ : γ => V) W) (v : β → V) :
    extend (PowerSeriesModule.partialEquiv e f v) =
      PowerSeriesModule.partialEquiv e (extend f) (fun j => single 0 (v j)) := by
  have hsum (L : α → ℤ) :
      (∑ i : γ, Sum.elim L (fun _ : β => (0 : ℤ)) (e.symm i)) = ∑ i, L i := by
    simpa only [Equiv.symm_apply_apply, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      Finset.sum_const_zero, add_zero] using
      (e.sum_comp (fun i => Sum.elim L (fun _ : β => (0 : ℤ)) (e.symm i))).symm
  apply multilinear_ext_of_bounded _ _ 0
  · intro x L hx
    simpa only [add_zero, extend_apply] using
      boundedBelow_applyMultilinear (PowerSeriesModule.partialEquiv e f v) x hx
  · intro x L hx
    change BoundedBelow ((∑ i, L i) + 0)
      (applyMultilinear f (fun i => Sum.elim x (fun j => single 0 (v j)) (e.symm i)))
    have hb : ∀ i : γ, BoundedBelow (Sum.elim L (fun _ : β => (0 : ℤ)) (e.symm i))
        (Sum.elim x (fun j => single 0 (v j)) (e.symm i)) := by
      intro i
      cases e.symm i with
      | inl j => exact hx j
      | inr j => exact boundedBelow_single 0 (v j)
    simpa only [hsum, add_zero] using boundedBelow_applyMultilinear f _ hb
  · intro L w
    change applyMultilinear (PowerSeriesModule.partialEquiv e f v) (fun i => single (L i) (w i)) =
      applyMultilinear f (fun i => Sum.elim (fun j => single (L j) (w j))
        (fun j => single 0 (v j)) (e.symm i))
    have he : (fun i => Sum.elim (fun j => single (L j) (w j))
        (fun j => single (k := k) 0 (v j)) (e.symm i)) =
        fun i => single (Sum.elim L (fun _ : β => (0 : ℤ)) (e.symm i))
          (Sum.elim w v (e.symm i)) := by
      funext i
      cases e.symm i <;> rfl
    rw [he, applyMultilinear_single, applyMultilinear_single, hsum]
    rfl

/-- Actual Laurent inputs may vary independently in every selected slot. -/
theorem applyMultilinear_partialEquiv {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (e : α ⊕ β ≃ γ) (f : MultilinearMap k (fun _ : γ => V) W) (v : β → V)
    (x : α → LaurentModule k V) :
    applyMultilinear (PowerSeriesModule.partialEquiv e f v) x =
      applyMultilinear f (fun i => Sum.elim x (fun j => single 0 (v j)) (e.symm i)) :=
  congrArg (fun F => F x) (extend_partialEquiv e f v)

/-- The native increasing finite-subset ordering is retained by Laurent partial evaluation. -/
theorem applyMultilinear_partialFinset {m n j : ℕ} {s : Finset (Fin m)}
    (hs : s.card = n) (hc : sᶜ.card = j)
    (f : MultilinearMap k (fun _ : Fin m => V) W) (v : Fin j → V)
    (x : Fin n → LaurentModule k V) :
    applyMultilinear (PowerSeriesModule.partialFinset hs hc f v) x =
      applyMultilinear f (fun i => Sum.elim x (fun q => single 0 (v q))
        ((finSumEquivOfFinset hs hc).symm i)) :=
  applyMultilinear_partialEquiv (finSumEquivOfFinset hs hc) f v x

private theorem prod_scalar_single {ι : Type*} [Fintype ι] (d : ι → ℤ) :
    (∏ i, (HahnSeries.single (d i) (1 : k) : LaurentSeries k)) =
      HahnSeries.single (∑ i, d i) (1 : k) := by
  have h (s : Finset ι) : (∏ i ∈ s, (HahnSeries.single (d i) (1 : k) : LaurentSeries k)) =
      HahnSeries.single (∑ i ∈ s, d i) (1 : k) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih => simp [hi, ih]
  exact h Finset.univ

/-- Fixed monomials may have independent integer exponents; their sum is the exact
Laurent shift multiplying the true partial evaluation. -/
theorem applyMultilinear_partialEquiv_single {α β γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    (e : α ⊕ β ≃ γ) (f : MultilinearMap k (fun _ : γ => V) W) (v : β → V)
    (d : β → ℤ) (x : α → LaurentModule k V) :
    applyMultilinear f (fun i => Sum.elim x (fun j => single (d j) (v j)) (e.symm i)) =
      (HahnSeries.single (∑ j, d j) (1 : k) : LaurentSeries k) •
        applyMultilinear (PowerSeriesModule.partialEquiv e f v) x := by
  let c : γ → LaurentSeries k :=
    fun i => Sum.elim (fun _ : α => 1) (fun j => HahnSeries.single (d j) 1) (e.symm i)
  let y : γ → LaurentModule k V := fun i => Sum.elim x (fun j => single 0 (v j)) (e.symm i)
  have he : (fun i => Sum.elim x (fun j => single (d j) (v j)) (e.symm i)) =
      fun i => c i • y i := by
    funext i
    dsimp [c, y]
    cases e.symm i with
    | inl j => simp
    | inr j => exact single_as_series_smul (d j) (v j)
  have hc : (∏ i, c i) = (HahnSeries.single (∑ j, d j) (1 : k) : LaurentSeries k) := by
    rw [← e.prod_comp c]
    simpa only [c, Equiv.symm_apply_apply, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr,
      Finset.prod_const_one, one_mul] using prod_scalar_single (k := k) d
  rw [he]
  change (extendScalars f) (fun i => c i • y i) = _
  rw [MultilinearMap.map_smul_univ, hc, applyMultilinear_partialEquiv]
  rfl

/-- The finite-subset version uses the actual ordered selected and complementary slots. -/
theorem applyMultilinear_partialFinset_single {m n j : ℕ} {s : Finset (Fin m)}
    (hs : s.card = n) (hc : sᶜ.card = j)
    (f : MultilinearMap k (fun _ : Fin m => V) W) (v : Fin j → V)
    (d : Fin j → ℤ) (x : Fin n → LaurentModule k V) :
    applyMultilinear f (fun i => Sum.elim x (fun q => single (d q) (v q))
      ((finSumEquivOfFinset hs hc).symm i)) =
      (HahnSeries.single (∑ q, d q) (1 : k) : LaurentSeries k) •
        applyMultilinear (PowerSeriesModule.partialFinset hs hc f v) x :=
  applyMultilinear_partialEquiv_single (finSumEquivOfFinset hs hc) f v d x

/-- Laurent extension preserves a genuine finite sum of coefficient cochains. -/
theorem extendScalars_finset_sum {α ι : Type*} [Fintype α]
    (s : Finset ι) (f : ι → MultilinearMap k (fun _ : α => V) W) :
    extendScalars (∑ i ∈ s, f i) = ∑ i ∈ s, extendScalars (f i) := by
  let A : MultilinearMap k (fun _ : α => V) W →+
      MultilinearMap (LaurentSeries k) (fun _ : α => LaurentModule k V) (LaurentModule k W) :=
    { toFun := extendScalars
      map_zero' := extendScalars_zero
      map_add' := extendScalars_add }
  exact map_sum A f s

end EnvelopingIsomorphism.FormalSeries.LaurentModule
