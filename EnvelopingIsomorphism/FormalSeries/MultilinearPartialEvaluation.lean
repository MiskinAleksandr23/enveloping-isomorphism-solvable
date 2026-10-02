import EnvelopingIsomorphism.FormalSeries.PowerSeriesModule
import EnvelopingIsomorphism.FormalSeries.Multilinear
import Mathlib.LinearAlgebra.Multilinear.Curry

/-! Completing a multilinear operation commutes with fixing constant-series inputs.
The argument is a finite coefficient reindexing, with no spanning or continuity assumption.
-/

noncomputable section

namespace EnvelopingIsomorphism.FormalSeries.PowerSeriesModule

variable {k V W : Type*} [CommRing k] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W]

/-- Partial evaluation after identifying the variable and constant slots. -/
def partialEquiv {α β γ : Type*} (e : α ⊕ β ≃ γ)
    (f : MultilinearMap k (fun _ : γ ↦ V) W) (v : β → V) :
    MultilinearMap k (fun _ : α ↦ V) W :=
  (LaurentModule.evaluationLinear v).compMultilinearMap
    (MultilinearMap.currySum (f.domDomCongr e.symm))

@[simp] theorem partialEquiv_apply {α β γ : Type*} (e : α ⊕ β ≃ γ)
    (f : MultilinearMap k (fun _ : γ ↦ V) W) (v : β → V) (x : α → V) :
    partialEquiv e f v x = f (fun i ↦ Sum.elim x v (e.symm i)) := rfl

/-- Only the antidiagonal terms with zero constant-slot exponents contribute. -/
theorem applyMultilinear_partialEquiv {α β γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ] (e : α ⊕ β ≃ γ)
    (f : MultilinearMap k (fun _ : γ ↦ V) W) (v : β → V)
    (x : α → PowerSeriesModule k V) :
    applyMultilinear (partialEquiv e f v) x =
      applyMultilinear f (fun i ↦ Sum.elim x (fun j ↦ single 0 (v j)) (e.symm i)) := by
  classical
  apply PowerSeriesModule.ext
  intro r
  simp only [coeffV_applyMultilinear, partialEquiv_apply]
  let insert : (α → ℕ) → γ → ℕ := fun a i ↦ Sum.elim a (fun _ ↦ 0) (e.symm i)
  let restrict : (γ → ℕ) → α → ℕ := fun b i ↦ b (e (Sum.inl i))
  let D : Finset (γ → ℕ) := Finset.piAntidiag Finset.univ r
  let T : Finset (γ → ℕ) := D.filter (fun b ↦ ∀ j, b (e (Sum.inr j)) = 0)
  let g : (γ → ℕ) → W := fun b ↦ f
    (fun i ↦ coeffV (b i) (Sum.elim x (fun j ↦ single 0 (v j)) (e.symm i)))
  have sum_split (b : γ → ℕ) :
      ∑ i, b i = (∑ i : α, b (e (Sum.inl i))) + ∑ j : β, b (e (Sum.inr j)) := by
    simpa only [Fintype.sum_sum_type] using (e.sum_comp b).symm
  have inserted_sum (a : α → ℕ) : ∑ i, insert a i = ∑ i, a i := by
    rw [sum_split]
    simp [insert]
  have restrict_insert (a : α → ℕ) : restrict (insert a) = a := by
    funext i
    simp [restrict, insert]
  have insert_restrict (b : γ → ℕ) (hb : b ∈ T) : insert (restrict b) = b := by
    have hz := (Finset.mem_filter.mp hb).2
    funext i
    obtain ⟨i, rfl⟩ := e.surjective i
    cases i with
    | inl i => simp [insert, restrict]
    | inr j => simp [insert, hz j]
  have hg (a : α → ℕ) :
      f (fun i ↦ Sum.elim (fun j ↦ coeffV (a j) (x j)) v (e.symm i)) = g (insert a) := by
    congr 1
    funext i
    obtain ⟨i, rfl⟩ := e.surjective i
    cases i <;> simp [insert]
  calc
    _ = ∑ b ∈ T, g b := by
      apply Finset.sum_nbij' insert restrict
      · intro a ha
        simp only [T, D, Finset.mem_filter, Finset.mem_piAntidiag,
          Finset.mem_univ, implies_true, and_true]
        refine ⟨?_, ?_⟩
        · rw [inserted_sum]
          exact (Finset.mem_piAntidiag.mp ha).1
        · intro j
          simp [insert]
      · intro b hb
        apply Finset.mem_piAntidiag.mpr
        refine ⟨?_, by simp⟩
        rw [← inserted_sum, insert_restrict b hb]
        exact (Finset.mem_piAntidiag.mp (Finset.mem_filter.mp hb).1).1
      · intro a ha
        exact restrict_insert a
      · exact insert_restrict
      · intro a ha
        exact hg a
    _ = _ := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro b hb hnot
      have hbad : ¬ ∀ j, b (e (Sum.inr j)) = 0 := by
        intro hz
        exact hnot (Finset.mem_filter.mpr ⟨hb, hz⟩)
      obtain ⟨j, hj⟩ := not_forall.mp hbad
      apply f.map_coord_zero (e (Sum.inr j))
      simp [hj]

/-- The native finite-subset curry equivalence followed by evaluation at the fixed inputs. -/
def partialFinset {m n j : ℕ} {s : Finset (Fin m)} (hs : s.card = n) (hc : sᶜ.card = j)
    (f : MultilinearMap k (fun _ : Fin m ↦ V) W) (v : Fin j → V) :
    MultilinearMap k (fun _ : Fin n ↦ V) W :=
  (LaurentModule.evaluationLinear v).compMultilinearMap
    (MultilinearMap.curryFinFinset k W V hs hc f)

@[simp] theorem partialFinset_apply {m n j : ℕ} {s : Finset (Fin m)}
    (hs : s.card = n) (hc : sᶜ.card = j)
    (f : MultilinearMap k (fun _ : Fin m ↦ V) W) (v : Fin j → V) (x : Fin n → V) :
    partialFinset hs hc f v x =
      f (fun i ↦ Sum.elim x v ((finSumEquivOfFinset hs hc).symm i)) := rfl

theorem partialFinset_apply_diagonal {m n j : ℕ} {s : Finset (Fin m)}
    (hs : s.card = n) (hc : sᶜ.card = j)
    (f : MultilinearMap k (fun _ : Fin m ↦ V) W) (v x : V) :
    partialFinset hs hc f (fun _ ↦ v) (fun _ ↦ x) =
      f (s.piecewise (fun _ ↦ x) (fun _ ↦ v)) :=
  MultilinearMap.curryFinFinset_apply_const hs hc f x v

theorem applyMultilinear_partialFinset {m n j : ℕ} {s : Finset (Fin m)}
    (hs : s.card = n) (hc : sᶜ.card = j)
    (f : MultilinearMap k (fun _ : Fin m ↦ V) W) (v : Fin j → V)
    (x : Fin n → PowerSeriesModule k V) :
    applyMultilinear (partialFinset hs hc f v) x =
      applyMultilinear f (fun i ↦ Sum.elim x (fun q ↦ single 0 (v q))
        ((finSumEquivOfFinset hs hc).symm i)) :=
  applyMultilinear_partialEquiv (finSumEquivOfFinset hs hc) f v x

theorem applyMultilinear_partialFinset_diagonal {m n j : ℕ} {s : Finset (Fin m)}
    (hs : s.card = n) (hc : sᶜ.card = j)
    (f : MultilinearMap k (fun _ : Fin m ↦ V) W) (v : V) (x : PowerSeriesModule k V) :
    applyMultilinear (partialFinset hs hc f (fun _ ↦ v)) (fun _ ↦ x) =
      applyMultilinear f (s.piecewise (fun _ ↦ x) (fun _ ↦ single 0 v)) := by
  rw [applyMultilinear_partialFinset]
  change MultilinearMap.curryFinFinset (PowerSeries k) (PowerSeriesModule k W)
      (PowerSeriesModule k V) hs hc (extendMultilinear f) (fun _ ↦ x) (fun _ ↦ single 0 v) = _
  exact MultilinearMap.curryFinFinset_apply_const hs hc (extendMultilinear f) x (single 0 v)

end EnvelopingIsomorphism.FormalSeries.PowerSeriesModule
