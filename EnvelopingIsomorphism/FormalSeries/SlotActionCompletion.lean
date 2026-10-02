import EnvelopingIsomorphism.FormalSeries.LaurentBinaryComposition
import EnvelopingIsomorphism.FormalSeries.PowerSeriesGroupedMultilinear

/-! Actual Laurent and power-series completion of a bilinear action in one multilinear slot. -/

noncomputable section
set_option maxSynthPendingDepth 8
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.FormalSeries.SlotActionCompletion
open scoped BigOperators Classical
local instance (r : ℕ) : DecidableEq (Fin r) := Classical.decEq _
universe u
variable {k V Y W : Type u} [CommRing k] [AddCommGroup V] [Module k V]
  [AddCommGroup Y] [Module k Y] [AddCommGroup W] [Module k W] {n : ℕ}

def slotLinear (F : MultilinearMap k (fun _ : Fin n ↦ V) W)
    (A : Y →ₗ[k] V →ₗ[k] V) (i : Fin n) (R : Fin n → V) : Y →ₗ[k] W where
  toFun X := F (Function.update R i (A X (R i)))
  map_add' X Y := by rw [map_add, LinearMap.add_apply, F.map_update_add]
  map_smul' c X := by
    rw [map_smul, LinearMap.smul_apply, F.map_update_smul]
    rfl

@[simp] theorem slotLinear_apply (F : MultilinearMap k (fun _ : Fin n ↦ V) W)
    (A : Y →ₗ[k] V →ₗ[k] V) (i : Fin n) (R : Fin n → V) (X : Y) :
    slotLinear F A i R X = F (Function.update R i (A X (R i))) := rfl

def actionSlot (F : MultilinearMap k (fun _ : Fin n ↦ V) W) (A : Y →ₗ[k] V →ₗ[k] V) (i : Fin n) :
    MultilinearMap k (fun _ : Fin n ↦ V) (Y →ₗ[k] W) :=
  MultilinearMap.mk' (slotLinear F A i) (by
    intro R j u v
    apply LinearMap.ext
    intro X
    simp only [slotLinear_apply, LinearMap.add_apply]
    by_cases hj : j = i
    · subst j
      simp only [Function.update_self, Function.update_idem, map_add, F.map_update_add]
    · simp only [Function.update_of_ne (Ne.symm hj)]
      rw [Function.update_comm hj, F.map_update_add]
      rw [Function.update_comm hj, Function.update_comm hj]
  ) (by
    intro R j c v
    apply LinearMap.ext
    intro X
    simp only [slotLinear_apply, LinearMap.smul_apply]
    by_cases hj : j = i
    · subst j
      simp only [Function.update_self, Function.update_idem, map_smul, F.map_update_smul]
    · simp only [Function.update_of_ne (Ne.symm hj)]
      rw [Function.update_comm hj, F.map_update_smul, Function.update_comm hj]

  )

@[simp] theorem actionSlot_apply (F : MultilinearMap k (fun _ : Fin n ↦ V) W)
    (A : Y →ₗ[k] V →ₗ[k] V) (i : Fin n) (R : Fin n → V) (X : Y) :
    actionSlot F A i R X = F (Function.update R i (A X (R i))) := rfl


private theorem powerCoeff_update (R : Fin n → PowerSeriesModule k V) (i : Fin n)
    (Z : PowerSeriesModule k V) (a : Fin n → ℕ) :
    (fun j ↦ PowerSeriesModule.coeffV (a j) (Function.update R i Z j)) =
      Function.update (fun j ↦ PowerSeriesModule.coeffV (a j) (R j)) i (PowerSeriesModule.coeffV (a i) Z) := by
  funext j
  by_cases hj : j = i <;> simp [hj]

theorem power_actionSlot (F : MultilinearMap k (fun _ : Fin n ↦ V) W)
    (A : Y →ₗ[k] V →ₗ[k] V) (i : Fin n) (R : Fin n → PowerSeriesModule k V)
    (X : PowerSeriesModule k Y) :
    PowerSeriesModule.applyBilinear (LinearMap.id : (Y →ₗ[k] W) →ₗ[k] Y →ₗ[k] W)
      (PowerSeriesModule.applyMultilinear (actionSlot F A i) R) X =
    PowerSeriesModule.applyMultilinear F (Function.update R i (PowerSeriesModule.applyBilinear A X (R i))) := by
  apply PowerSeriesModule.ext
  intro D
  let g (r : ℕ) (a : Fin n → ℕ) := F
    (Function.update (fun j ↦ PowerSeriesModule.coeffV (a j) (R j)) i
      (A (PowerSeriesModule.coeffV r X) (PowerSeriesModule.coeffV (a i) (R i))))
  have hr : PowerSeriesModule.coeffV D
      (PowerSeriesModule.applyMultilinear F (Function.update R i (PowerSeriesModule.applyBilinear A X (R i)))) =
      ∑ a ∈ Finset.piAntidiag Finset.univ D,
        ∑ rs ∈ Finset.HasAntidiagonal.antidiagonal (a i), g rs.1 (Function.update a i rs.2) := by
    simp only [PowerSeriesModule.coeffV_applyMultilinear, powerCoeff_update,
      PowerSeriesModule.coeffV_applyBilinear, F.map_update_sum]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro rs hrs
    dsimp only [g]
    simp only [Function.update_self]
    apply congrArg F
    funext j
    by_cases hj : j = i <;> simp [hj]
  rw [hr, PowerSeriesModule.sum_piAntidiag_split g D i]
  simp only [PowerSeriesModule.coeffV_applyBilinear, PowerSeriesModule.coeffV_applyMultilinear,
    LinearMap.id_apply, LinearMap.sum_apply, actionSlot_apply]
  exact (Finset.Nat.sum_antidiagonal_swap (n := D)
    (f := fun p ↦ ∑ a ∈ Finset.piAntidiag Finset.univ p.1, g p.2 a)).symm


def mixedExtend (C : MultilinearMap k (fun _ : Fin n ↦ V) (Y →ₗ[k] W)) :
    MultilinearMap (LaurentSeries k) (fun _ : Fin n ↦ LaurentModule k V)
      (LaurentModule k Y →ₗ[LaurentSeries k] LaurentModule k W) :=
  LaurentModule.linearApply.compMultilinearMap (LaurentModule.extendScalars C)

@[simp] theorem mixedExtend_apply (C : MultilinearMap k (fun _ : Fin n ↦ V) (Y →ₗ[k] W))
    (R : Fin n → LaurentModule k V) (X : LaurentModule k Y) :
    mixedExtend C R X = LaurentModule.linearApply (LaurentModule.applyMultilinear C R) X := rfl

theorem mixedExtend_bound (C : MultilinearMap k (fun _ : Fin n ↦ V) (Y →ₗ[k] W))
    (R : Fin n → LaurentModule k V) (X : LaurentModule k Y)
    (b : Fin n → ℤ) (c : ℤ) (hR : ∀ j, LaurentModule.BoundedBelow (b j) (R j))
    (hX : LaurentModule.BoundedBelow c X) :
    LaurentModule.BoundedBelow ((∑ j, b j) + c) (mixedExtend C R X) :=
  LaurentModule.boundedBelow_linearApply _ _ (LaurentModule.boundedBelow_applyMultilinear C R hR) hX

theorem sum_update_add (b : Fin n → ℤ) (i : Fin n) (c : ℤ) :
    (∑ j, Function.update b i (c + b i) j) = (∑ j, b j) + c := by
  rw [Finset.sum_update_of_mem (Finset.mem_univ i), Finset.sdiff_singleton_eq_erase]
  have h := Finset.sum_erase_add Finset.univ b (Finset.mem_univ i)
  omega

theorem laurent_actionSlot_bound (F : MultilinearMap k (fun _ : Fin n ↦ V) W)
    (A : Y →ₗ[k] V →ₗ[k] V) (i : Fin n)
    (R : Fin n → LaurentModule k V) (X : LaurentModule k Y)
    (b : Fin n → ℤ) (c : ℤ) (hR : ∀ j, LaurentModule.BoundedBelow (b j) (R j))
    (hX : LaurentModule.BoundedBelow c X) :
    LaurentModule.BoundedBelow ((∑ j, b j) + c)
      (actionSlot (LaurentModule.extendScalars F) (LaurentModule.extendBilinear A) i R X) := by
  have hargs : ∀ j, LaurentModule.BoundedBelow (Function.update b i (c + b i) j)
      (Function.update R i (LaurentModule.extendBilinear A X (R i)) j) := by
    intro j
    by_cases hj : j = i
    · subst j
      simp only [Function.update_self]
      exact LaurentModule.boundedBelow_extendBilinear A _ _ hX (hR i)
    · simpa only [Function.update_of_ne hj] using hR j
  have h := LaurentModule.boundedBelow_applyMultilinear F _ hargs
  rw [sum_update_add] at h
  exact h

theorem laurent_actionSlot_single (F : MultilinearMap k (fun _ : Fin n ↦ V) W)
    (A : Y →ₗ[k] V →ₗ[k] V) (i : Fin n) (b : Fin n → ℤ) (R : Fin n → V)
    (c : ℤ) (X : Y) :
    mixedExtend (actionSlot F A i) (fun j ↦ LaurentModule.single (b j) (R j)) (LaurentModule.single c X) =
      actionSlot (LaurentModule.extendScalars F) (LaurentModule.extendBilinear A) i
        (fun j ↦ LaurentModule.single (b j) (R j)) (LaurentModule.single c X) := by
  rw [mixedExtend_apply, LaurentModule.applyMultilinear_single, LaurentModule.linearApply_single,
    actionSlot_apply, actionSlot_apply, LaurentModule.extendBilinear_single]
  change LaurentModule.single ((∑ j, b j) + c) (F (Function.update R i (A X (R i)))) =
    LaurentModule.applyMultilinear F (Function.update (fun j ↦ LaurentModule.single (b j) (R j)) i
      (LaurentModule.single (c + b i) (A X (R i))))
  have he : Function.update (fun j ↦ LaurentModule.single (k := k) (b j) (R j)) i
      (LaurentModule.single (c + b i) (A X (R i))) =
      fun j ↦ LaurentModule.single (Function.update b i (c + b i) j) (Function.update R i (A X (R i)) j) := by
    funext j
    by_cases hj : j = i <;> simp [hj]
  rw [he, LaurentModule.applyMultilinear_single, sum_update_add]

theorem laurent_actionSlot (F : MultilinearMap k (fun _ : Fin n ↦ V) W)
    (A : Y →ₗ[k] V →ₗ[k] V) (i : Fin n) :
    mixedExtend (actionSlot F A i) =
      actionSlot (LaurentModule.extendScalars F) (LaurentModule.extendBilinear A) i := by
  apply MultilinearMap.ext
  intro R
  apply LinearMap.ext
  intro X
  obtain ⟨c, hc⟩ := LaurentModule.exists_bound X
  let L := mixedExtend (actionSlot F A i)
  let G := actionSlot (LaurentModule.extendScalars F) (LaurentModule.extendBilinear A) i
  have he : ((LinearMap.applyₗ X).compMultilinearMap L).restrictScalars k =
      ((LinearMap.applyₗ X).compMultilinearMap G).restrictScalars k := by
    apply LaurentModule.multilinear_ext_of_bounded _ _ c
    · intro S b hS
      exact mixedExtend_bound (actionSlot F A i) S X b c hS hc
    · intro S b hS
      exact laurent_actionSlot_bound F A i S X b c hS hc
    · intro b v
      have hl : (L (fun j ↦ LaurentModule.single (b j) (v j))).restrictScalars k =
          (G (fun j ↦ LaurentModule.single (b j) (v j))).restrictScalars k := by
        apply LaurentModule.linear_ext_of_bounded _ _ (∑ j, b j)
        · intro d Y hY
          change LaurentModule.BoundedBelow (d + ∑ j, b j)
            (mixedExtend (actionSlot F A i) (fun j ↦ LaurentModule.single (b j) (v j)) Y)
          simpa only [add_comm] using mixedExtend_bound (actionSlot F A i)
            (fun j ↦ LaurentModule.single (b j) (v j)) Y b d
            (fun j ↦ LaurentModule.boundedBelow_single _ _) hY
        · intro d Y hY
          change LaurentModule.BoundedBelow (d + ∑ j, b j)
            (actionSlot (LaurentModule.extendScalars F) (LaurentModule.extendBilinear A) i
              (fun j ↦ LaurentModule.single (b j) (v j)) Y)
          simpa only [add_comm] using laurent_actionSlot_bound F A i
            (fun j ↦ LaurentModule.single (b j) (v j)) Y b d
            (fun j ↦ LaurentModule.boundedBelow_single _ _) hY
        · intro d Y
          exact laurent_actionSlot_single F A i b v d Y
      exact congrArg (fun T ↦ T X) hl
  exact congrArg (fun T ↦ T R) he


private theorem power_eval_map
    (P : PowerSeriesModule (LaurentSeries k) (LaurentModule k (Y →ₗ[k] W)))
    (X : PowerSeriesModule (LaurentSeries k) (LaurentModule k Y)) :
    PowerSeriesModule.applyBilinear
      (LinearMap.id : (LaurentModule k Y →ₗ[LaurentSeries k] LaurentModule k W) →ₗ[LaurentSeries k]
        LaurentModule k Y →ₗ[LaurentSeries k] LaurentModule k W)
      (PowerSeriesModule.map LaurentModule.linearApply P) X =
      PowerSeriesModule.applyBilinear LaurentModule.linearApply P X := by
  apply PowerSeriesModule.ext
  intro d
  simp only [PowerSeriesModule.coeffV_applyBilinear, PowerSeriesModule.coeffV_map, LinearMap.id_apply]

theorem double_actionSlot (F : MultilinearMap k (fun _ : Fin n ↦ V) W)
    (A : Y →ₗ[k] V →ₗ[k] V) (i : Fin n)
    (R : Fin n → PowerSeriesModule (LaurentSeries k) (LaurentModule k V))
    (X : PowerSeriesModule (LaurentSeries k) (LaurentModule k Y)) :
    PowerSeriesModule.applyBilinear LaurentModule.linearApply
      (PowerSeriesModule.applyMultilinear (LaurentModule.extendScalars (actionSlot F A i)) R) X =
      PowerSeriesModule.applyMultilinear (LaurentModule.extendScalars F)
        (Function.update R i (PowerSeriesModule.applyBilinear (LaurentModule.extendBilinear A) X (R i))) := by
  rw [← power_eval_map, PowerSeriesModule.applyMultilinear_postcomp]
  change PowerSeriesModule.applyBilinear LinearMap.id
    (PowerSeriesModule.applyMultilinear (mixedExtend (actionSlot F A i)) R) X = _
  rw [laurent_actionSlot]
  exact power_actionSlot (LaurentModule.extendScalars F) (LaurentModule.extendBilinear A) i R X

end EnvelopingIsomorphism.FormalSeries.SlotActionCompletion
