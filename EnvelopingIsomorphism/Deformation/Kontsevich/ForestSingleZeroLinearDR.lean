import EnvelopingIsomorphism.Deformation.Kontsevich.SubtreeForestInsertion
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Analysis.SpecificLimits.Basic

/-! At a single zero radius, the actual forest insertion is an exact linear
collision family in that radius. Its full resolved DR array is consequently
the literal two-level linear collision array. No DR identity is an input. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopingIsomorphism.Deformation.Kontsevich.ForestSingleZeroLinearDR
open scoped Classical BigOperators Topology
open Filter Set AncestorScaleRatios ForestInsertionDifference ForestDirectionRatioCoordinates
variable (T : RootedTree) [Fintype T]

/-- Coefficient of the selected radius in an ancestor product. -/
def scaleCoefficient (c : T) (ρ : T → ℝ) (v : T) : ℝ :=
  if c ≤ v then ∏ u ∈ (ancestors v).erase c, ρ u else 0

theorem scale_update (c : T) (ρ : T → ℝ) (hc : ρ c = 0) (t : ℝ) (v : T) :
    scale (Function.update ρ c t) v = scale ρ v + t * scaleCoefficient T c ρ v := by
  by_cases hcv : c ≤ v
  · have hm : c ∈ ancestors v := (mem_ancestors c v).mpr hcv
    have hz : scale ρ v = 0 := Finset.prod_eq_zero hm hc
    rw [hz, zero_add]
    simp [scale, Finset.prod_update_of_mem hm, scaleCoefficient, hcv, mul_comm, Finset.sdiff_singleton_eq_erase]
  · have hm : c ∉ ancestors v := by simpa using hcv
    simp [scale, Finset.prod_update_of_notMem hm, scaleCoefficient, hcv]

/-- The actual first-order displacement, written without division by any radius. -/
def velocity (c : T) (p : ForestDirectionRatioCoordinates.Parameters T) (v : T) : ℂ :=
  ∑ u ∈ (ancestors v).erase ⊥, scaleCoefficient T c p.1 (Order.pred u) • p.2 u

def perturb (c : T) (p : ForestDirectionRatioCoordinates.Parameters T) (t : ℝ) :
    ForestDirectionRatioCoordinates.Parameters T := (Function.update p.1 c t, p.2)

theorem position_perturb (c : T) (p : ForestDirectionRatioCoordinates.Parameters T)
    (hc : p.1 c = 0) (t : ℝ) (v : T) :
    position T (perturb T c p t).1 (perturb T c p t).2 v =
      position T p.1 p.2 v + t • velocity T c p v := by
  simp only [perturb, position, velocity, Finset.smul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u hu
  rw [scale_update T c p.1 hc, add_smul, mul_smul]

@[simp] theorem perturb_zero (c : T) (p : ForestDirectionRatioCoordinates.Parameters T) (hc : p.1 c = 0) :
    perturb T c p 0 = p := by
  rw [← hc]
  simp [perturb]

@[fun_prop] theorem continuous_perturb (c : T) (p : ForestDirectionRatioCoordinates.Parameters T) :
    Continuous (perturb T c p) := by
  apply Continuous.prodMk
  · apply continuous_pi
    intro v
    by_cases hv : v = c <;> simp [perturb, Function.update, hv] <;> fun_prop
  · exact continuous_const

theorem velocity_eq_zero_of_not_le (c : T) (p : ForestDirectionRatioCoordinates.Parameters T)
    (v : T) (hv : ¬c ≤ v) : velocity T c p v = 0 := by
  apply Finset.sum_eq_zero
  intro u hu
  have huv : u ≤ v := (mem_ancestors u v).mp (Finset.mem_of_mem_erase hu)
  have hn : ¬c ≤ Order.pred u := fun h ↦ hv (h.trans ((Order.pred_le u).trans huv))
  simp [scaleCoefficient, hn]

theorem velocity_self (c : T) (p : ForestDirectionRatioCoordinates.Parameters T) :
    velocity T c p c = 0 := by
  apply Finset.sum_eq_zero
  intro u hu
  have hune : u ≠ ⊥ := (Finset.mem_erase.mp hu).1
  have huc : u ≤ c := (mem_ancestors u c).mp (Finset.mem_of_mem_erase hu)
  have hn : ¬c ≤ Order.pred u := fun h ↦
    (Order.pred_lt_iff_ne_bot.mpr hune).not_ge (huc.trans h)
  simp [scaleCoefficient, hn]

theorem residualScale_update (c : T) (ρ : T → ℝ) (t : ℝ) (v : T) :
    residualScale (Function.update ρ c t) c v = residualScale ρ c v := by
  apply Finset.prod_update_of_notMem
  simp

theorem branchUnit_update (c : T) (p : ForestDirectionRatioCoordinates.Parameters T) (t : ℝ) (v : T) :
    branchUnit T (Function.update p.1 c t) p.2 c v = branchUnit T p.1 p.2 c v := by
  simp only [branchUnit, residualScale_update]

/-- On the cluster the linear-family velocity is a single positive common
scale times the actual residual subtree insertion. -/
theorem velocity_eq_branchUnit (c : T) (p : ForestDirectionRatioCoordinates.Parameters T)
    (hc : p.1 c = 0) (v : T) (hv : c ≤ v) :
    velocity T c p v = scaleCoefficient T c p.1 c • branchUnit T p.1 p.2 c v := by
  have hz : scale p.1 c = 0 := Finset.prod_eq_zero (by simp) hc
  have hbase : position T p.1 p.2 v = position T p.1 p.2 c := by
    rw [position_factor_from_ancestor T p.1 p.2 hv, hz, zero_smul, add_zero]
  have h := position_factor_from_ancestor T (Function.update p.1 c 1) p.2 hv
  change position T (perturb T c p 1).1 (perturb T c p 1).2 v = _ at h
  rw [position_perturb T c p hc, one_smul, hbase] at h
  have hroot := position_perturb T c p hc 1 c
  simp only [perturb, velocity_self, smul_zero, add_zero] at hroot
  rw [hroot, scale_update T c p.1 hc, hz, zero_add, one_mul, branchUnit_update] at h
  exact add_left_cancel h

theorem scaleCoefficient_self_pos (c : T) (ρ : T → ℝ)
    (hpos : ∀ v, v ≠ c → 0 < ρ v) : 0 < scaleCoefficient T c ρ c := by
  simp only [scaleCoefficient, if_pos le_rfl]
  exact Finset.prod_pos (fun v hv ↦ hpos v (Finset.mem_erase.mp hv).1)

variable {I : Type*} (lab : I → T)

def linearData (base vel : I → ℂ) : Data I :=
  (fun e ↦ linearPhaseLimit (base e.val.2 - base e.val.1) (vel e.val.2 - vel e.val.1),
   fun e ↦ linearRatioLimit (base e.val.2.1 - base e.val.1) (base e.val.2.2 - base e.val.1)
     (vel e.val.2.1 - vel e.val.1) (vel e.val.2.2 - vel e.val.1))

theorem pairDifference_perturb (c : T) (p : ForestDirectionRatioCoordinates.Parameters T)
    (hc : p.1 c = 0) (t : ℝ) (e : Pair I) :
    pairDifference T lab (perturb T c p t) e = pairDifference T lab p e +
      (t : ℂ) * (velocity T c p (lab e.val.2) - velocity T c p (lab e.val.1)) := by
  unfold pairDifference
  rw [position_perturb T c p hc, position_perturb T c p hc]
  simp only [Complex.real_smul]
  ring

def shrinking (k : ℕ) : ℝ := 1 / ((k : ℝ) + 1)

lemma shrinking_pos (k : ℕ) : 0 < shrinking k := by unfold shrinking; positivity
lemma tendsto_shrinking : Tendsto shrinking atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

/-- Full direction/ratio equality for the exact two-level collision family.
It follows from positive-radius equality and uniqueness of the actual limits. -/
theorem resolvedCoordinates_eq_linearData (c : T) (p : Domain T lab)
    (hc : p.val.1 c = 0) (hpos : ∀ v, v ≠ c → 0 < p.val.1 v) :
    resolvedCoordinates T lab p =
      linearData (fun j ↦ position T p.val.1 p.val.2 (lab j))
        (fun j ↦ velocity T c p.val (lab j)) := by
  have ht : Tendsto (fun k ↦ perturb T c p.val (shrinking k)) atTop (𝓝 p.val) := by
    have h := ((continuous_perturb T c p.val).tendsto 0).comp tendsto_shrinking
    simpa only [perturb_zero T c p.val hc, Function.comp_def] using h
  have hp (k : ℕ) (v : T) : 0 < (perturb T c p.val (shrinking k)).1 v := by
    by_cases hv : v = c
    · subst v
      simpa [perturb] using shrinking_pos k
    · simpa [perturb, hv] using hpos v hv
  apply Prod.ext
  · funext e
    have h₁ := ((continuousAt_direction T lab p.val e (p.property.2 e)).tendsto).comp ht
    have h₂ := tendsto_linearPhaseLimit tendsto_shrinking
      (Filter.Eventually.of_forall shrinking_pos) (pairDifference T lab p.val e)
      (velocity T c p.val (lab e.val.2) - velocity T c p.val (lab e.val.1))
    have he : (fun k ↦ direction T lab (perturb T c p.val (shrinking k)) e) =
        (fun k ↦ complexPhase (pairDifference T lab p.val e + (shrinking k : ℂ) *
          (velocity T c p.val (lab e.val.2) - velocity T c p.val (lab e.val.1)))) := by
      funext k
      rw [direction_eq_actual T lab _ (hp k), pairDifference_perturb T lab c p.val hc]
    simp only [Function.comp_def] at h₁ h₂
    rw [he] at h₁
    exact tendsto_nhds_unique h₁ h₂
  · funext e
    apply Subtype.ext
    have h₁ := ((contDiffAt_ratioValue T lab p.val p.property e).continuousAt.tendsto).comp ht
    have h₂ := (continuous_subtype_val.tendsto
      (linearRatioLimit (pairDifference T lab p.val (firstPair e))
        (pairDifference T lab p.val (secondPair e))
        (velocity T c p.val (lab e.val.2.1) - velocity T c p.val (lab e.val.1))
        (velocity T c p.val (lab e.val.2.2) - velocity T c p.val (lab e.val.1)))).comp
      (tendsto_linearRatioLimit tendsto_shrinking (Filter.Eventually.of_forall shrinking_pos)
        (pairDifference T lab p.val (firstPair e)) (pairDifference T lab p.val (secondPair e))
        (velocity T c p.val (lab e.val.2.1) - velocity T c p.val (lab e.val.1))
        (velocity T c p.val (lab e.val.2.2) - velocity T c p.val (lab e.val.1)))
    have he : (fun k ↦ ratioValue T lab (perturb T c p.val (shrinking k)) e) =
      (fun k ↦ ((normalizedNormRatio
        (pairDifference T lab p.val (firstPair e) + (shrinking k : ℂ) *
          (velocity T c p.val (lab e.val.2.1) - velocity T c p.val (lab e.val.1)))
        (pairDifference T lab p.val (secondPair e) + (shrinking k : ℂ) *
          (velocity T c p.val (lab e.val.2.2) - velocity T c p.val (lab e.val.1)))) : ℝ)) := by
      funext k
      rw [ratioValue_eq_actual T lab _ (hp k), pairDifference_perturb T lab c p.val hc,
        pairDifference_perturb T lab c p.val hc]
      rfl
    simp only [Function.comp_def] at h₁ h₂
    rw [he] at h₁
    exact tendsto_nhds_unique h₁ h₂

/-- Exact invariance under independent positive coarse and fine affine
normalizations, stated in the pair differences on which DR actually depends. -/
theorem linearData_eq_of_scaled_differences (base vel base' vel' : I → ℂ)
    (b s : ℝ) (hb : 0 < b) (hs : 0 < s)
    (hbase : ∀ e : Pair I, base' e.val.2 - base' e.val.1 =
      (b : ℂ) * (base e.val.2 - base e.val.1))
    (hvel : ∀ e : Pair I, base e.val.2 - base e.val.1 = 0 →
      vel' e.val.2 - vel' e.val.1 = (s : ℂ) * (vel e.val.2 - vel e.val.1)) :
    linearData base' vel' = linearData base vel := by
  have hbne : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb.ne'
  apply Prod.ext
  · funext e
    change linearPhaseLimit _ _ = linearPhaseLimit _ _
    rw [linearPhaseLimit, linearPhaseLimit, hbase e]
    by_cases h : base e.val.2 - base e.val.1 = 0
    · rw [h, mul_zero, if_pos rfl, if_pos rfl, hvel e h]
      exact complexPhase_pos_real_mul hs _
    · rw [if_neg (mul_ne_zero hbne h), if_neg h]
      exact complexPhase_pos_real_mul hb _
  · funext e
    change linearRatioLimit _ _ _ _ = linearRatioLimit _ _ _ _
    have hb₁ := hbase (firstPair e)
    have hb₂ := hbase (secondPair e)
    simp only [firstPair, secondPair] at hb₁ hb₂
    rw [linearRatioLimit, linearRatioLimit, hb₁, hb₂]
    by_cases h : base e.val.2.1 - base e.val.1 = 0 ∧ base e.val.2.2 - base e.val.1 = 0
    · have hv₁ := hvel (firstPair e) h.1
      have hv₂ := hvel (secondPair e) h.2
      simp only [firstPair, secondPair] at hv₁ hv₂
      rw [if_pos (by simpa only [mul_eq_zero, hbne, false_or] using h), if_pos h, hv₁, hv₂]
      exact normalizedNormRatio_pos_real_mul s hs _ _
    · rw [if_neg (by simpa only [mul_eq_zero, hbne, false_or] using h), if_neg h]
      exact normalizedNormRatio_pos_real_mul b hb _ _

def branchVelocity (c : T) (p : ForestDirectionRatioCoordinates.Parameters T) (v : T) : ℂ :=
  if c ≤ v then branchUnit T p.1 p.2 c v else 0

theorem velocity_eq_scaled_branch (c : T) (p : ForestDirectionRatioCoordinates.Parameters T)
    (hc : p.1 c = 0) (v : T) :
    velocity T c p v = scaleCoefficient T c p.1 c • branchVelocity T c p v := by
  by_cases hv : c ≤ v
  · rw [branchVelocity, if_pos hv]
    exact velocity_eq_branchUnit T c p hc v hv
  · rw [branchVelocity, if_neg hv, smul_zero]
    exact velocity_eq_zero_of_not_le T c p v hv

/-- The canonical two-level forest DR decomposition, with the global positive
coarse-to-cluster scale removed. The fine coordinates are actual branch sums. -/
theorem resolvedCoordinates_eq_branchData (c : T) (p : Domain T lab)
    (hc : p.val.1 c = 0) (hpos : ∀ v, v ≠ c → 0 < p.val.1 v) :
    resolvedCoordinates T lab p =
      linearData (fun j ↦ position T p.val.1 p.val.2 (lab j))
        (fun j ↦ branchVelocity T c p.val (lab j)) := by
  rw [resolvedCoordinates_eq_linearData T lab c p hc hpos]
  apply linearData_eq_of_scaled_differences _ _ _ _ 1 (scaleCoefficient T c p.val.1 c)
    zero_lt_one (scaleCoefficient_self_pos T c p.val.1 hpos)
  · intro e
    simp
  · intro e he
    simp only [velocity_eq_scaled_branch T c p.val hc, Complex.real_smul]
    ring

end EnvelopingIsomorphism.Deformation.Kontsevich.ForestSingleZeroLinearDR
