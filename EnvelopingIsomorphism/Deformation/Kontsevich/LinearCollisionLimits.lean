import EnvelopingIsomorphism.Deformation.Kontsevich.Compactification

/-!
# Limits of linear collision families in compact configuration coordinates

For a family whose doubled point coordinates are `base + r * velocity`, with
`r → 0` through positive values, every compact coordinate has an explicit limit.
Directions of colliding pairs retain their relative velocity; ratios with two
colliding distances retain the corresponding velocity-length ratio.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Kontsevich

open Configuration Filter Set Topology
open scoped Topology

/-- A bounded ratio of two complex-vector lengths, including zero lengths. -/
def normalizedNormRatio (a b : ℂ) : Set.Icc (0 : ℝ) 1 := by
  refine ⟨‖a‖ / (‖a‖ + ‖b‖), div_nonneg (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _)), ?_⟩
  by_cases h : ‖a‖ + ‖b‖ = 0
  · simp [h]
  · apply (div_le_one (lt_of_le_of_ne (add_nonneg (norm_nonneg _) (norm_nonneg _)) (Ne.symm h))).mpr
    exact le_add_of_nonneg_right (norm_nonneg _)

theorem normalizedNormRatio_pos_real_mul (r : ℝ) (hr : 0 < r) (a b : ℂ) :
    normalizedNormRatio ((r : ℂ) * a) ((r : ℂ) * b) = normalizedNormRatio a b := by
  apply Subtype.ext
  change ‖(r : ℂ) * a‖ / (‖(r : ℂ) * a‖ + ‖(r : ℂ) * b‖) = ‖a‖ / (‖a‖ + ‖b‖)
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  rw [← mul_add]
  exact mul_div_mul_left _ _ (ne_of_gt hr)

theorem continuousAt_normalizedNormRatio (a b : ℂ) (h : ¬ (a = 0 ∧ b = 0)) :
    ContinuousAt (fun p : ℂ × ℂ => normalizedNormRatio p.1 p.2) (a, b) := by
  have hd : ‖a‖ + ‖b‖ ≠ 0 := by
    intro he
    have ha : ‖a‖ = 0 := by linarith [norm_nonneg a, norm_nonneg b]
    have hb : ‖b‖ = 0 := by linarith [norm_nonneg a, norm_nonneg b]
    exact h ⟨norm_eq_zero.mp ha, norm_eq_zero.mp hb⟩
  apply tendsto_subtype_rng.mpr
  exact continuousAt_fst.norm.div (continuousAt_fst.norm.add continuousAt_snd.norm) hd

def linearPhaseLimit (a b : ℂ) : Circle := if a = 0 then complexPhase b else complexPhase a

def linearRatioLimit (a₁ a₂ b₁ b₂ : ℂ) : Set.Icc (0 : ℝ) 1 :=
  if a₁ = 0 ∧ a₂ = 0 then normalizedNormRatio b₁ b₂ else normalizedNormRatio a₁ a₂

variable {α : Type*} {l : Filter α} {r : α → ℝ}

theorem tendsto_linear_complex (hr : Tendsto r l (𝓝 0)) (a b : ℂ) :
    Tendsto (fun x => a + (r x : ℂ) * b) l (𝓝 a) := by
  simpa using tendsto_const_nhds.add
    (((Complex.continuous_ofReal.tendsto 0).comp hr).mul (tendsto_const_nhds (x := b)))

theorem tendsto_linearPhaseLimit (hr : Tendsto r l (𝓝 0))
    (hpos : ∀ᶠ x in l, 0 < r x) (a b : ℂ) :
    Tendsto (fun x => complexPhase (a + (r x : ℂ) * b)) l (𝓝 (linearPhaseLimit a b)) := by
  by_cases ha : a = 0
  · rw [linearPhaseLimit, if_pos ha]
    have heq : (fun x => complexPhase (a + (r x : ℂ) * b)) =ᶠ[l] fun _ => complexPhase b :=
      hpos.mono fun x hx => by simpa only [ha, zero_add] using complexPhase_pos_real_mul hx b
    exact tendsto_const_nhds.congr' heq.symm
  · rw [linearPhaseLimit, if_neg ha]
    exact (continuousAt_complexPhase ha).tendsto.comp (tendsto_linear_complex hr a b)

theorem tendsto_linearRatioLimit (hr : Tendsto r l (𝓝 0))
    (hpos : ∀ᶠ x in l, 0 < r x) (a₁ a₂ b₁ b₂ : ℂ) :
    Tendsto (fun x => normalizedNormRatio (a₁ + (r x : ℂ) * b₁) (a₂ + (r x : ℂ) * b₂))
      l (𝓝 (linearRatioLimit a₁ a₂ b₁ b₂)) := by
  by_cases ha : a₁ = 0 ∧ a₂ = 0
  · rw [linearRatioLimit, if_pos ha]
    have heq : (fun x => normalizedNormRatio (a₁ + (r x : ℂ) * b₁) (a₂ + (r x : ℂ) * b₂))
        =ᶠ[l] fun _ => normalizedNormRatio b₁ b₂ :=
      hpos.mono fun x hx => by
        simpa only [ha.1, ha.2, zero_add] using normalizedNormRatio_pos_real_mul (r x) hx b₁ b₂
    exact tendsto_const_nhds.congr' heq.symm
  · rw [linearRatioLimit, if_neg ha]
    have hp : Tendsto (fun x => (a₁ + (r x : ℂ) * b₁, a₂ + (r x : ℂ) * b₂))
        l (𝓝 (a₁, a₂)) :=
      (tendsto_linear_complex hr a₁ b₁).prodMk_nhds (tendsto_linear_complex hr a₂ b₂)
    have hc : Tendsto (fun p : ℂ × ℂ => normalizedNormRatio p.1 p.2)
        (𝓝 (a₁, a₂)) (𝓝 (normalizedNormRatio a₁ a₂)) :=
      continuousAt_normalizedNormRatio a₁ a₂ ha
    simpa only [Function.comp_def] using hc.comp hp

variable {n m : ℕ}

/-- The explicit compact coordinate retained by a first-order collision family. -/
def linearCollisionCoordinates (base velocity : DoubledLabel n m → ℂ) : CompactCoordinateSpace n m :=
  ((fun v => (base (Sum.inl v) : OnePoint ℂ)),
    (fun p => linearPhaseLimit (base p.val.2 - base p.val.1)
      (velocity p.val.2 - velocity p.val.1)),
    (fun t => linearRatioLimit (base t.val.2.1 - base t.val.1)
      (base t.val.2.2 - base t.val.1) (velocity t.val.2.1 - velocity t.val.1)
      (velocity t.val.2.2 - velocity t.val.1)))

/-- For a fixed collision pattern, varying its nondegenerate velocities continuously
varies the retained compact coordinate. -/
theorem continuous_linearCollisionCoordinates {U : Type*} [TopologicalSpace U]
    (base : DoubledLabel n m → ℂ) (velocity : U → DoubledLabel n m → ℂ)
    (hv : ∀ j, Continuous (fun u => velocity u j))
    (hne : ∀ u (p : DoubledPair n m), base p.val.2 - base p.val.1 = 0 →
      velocity u p.val.2 - velocity u p.val.1 ≠ 0) :
    Continuous (fun u => linearCollisionCoordinates base (velocity u)) := by
  apply Continuous.prodMk
  · exact continuous_pi fun _ => continuous_const
  · apply Continuous.prodMk
    · apply continuous_pi
      intro p
      by_cases hp : base p.val.2 - base p.val.1 = 0
      · change Continuous (fun u => linearPhaseLimit _ _)
        simp only [linearPhaseLimit, if_pos hp]
        apply continuous_iff_continuousAt.mpr
        intro u
        exact (continuousAt_complexPhase (hne u p hp)).comp
          (f := fun w => velocity w p.val.2 - velocity w p.val.1) (x := u)
          ((hv p.val.2).sub (hv p.val.1)).continuousAt
      · simpa only [linearCollisionCoordinates, linearPhaseLimit, if_neg hp] using
          (continuous_const : Continuous (fun _ : U => complexPhase (base p.val.2 - base p.val.1)))
    · apply continuous_pi
      intro t
      by_cases ht : base t.val.2.1 - base t.val.1 = 0 ∧ base t.val.2.2 - base t.val.1 = 0
      · change Continuous (fun u => linearRatioLimit _ _ _ _)
        simp only [linearRatioLimit, if_pos ht]
        apply continuous_iff_continuousAt.mpr
        intro u
        have hn : ¬ (velocity u t.val.2.1 - velocity u t.val.1 = 0 ∧
            velocity u t.val.2.2 - velocity u t.val.1 = 0) :=
          fun h => hne u ⟨(t.val.1, t.val.2.1), t.property.1⟩ ht.1 h.1
        have hc := continuousAt_normalizedNormRatio _ _ hn
        have hpair := ((hv t.val.2.1).sub (hv t.val.1)).prodMk
          ((hv t.val.2.2).sub (hv t.val.1))
        simpa only [Function.comp_def] using hc.comp
          (f := fun w : U => (velocity w t.val.2.1 - velocity w t.val.1,
            velocity w t.val.2.2 - velocity w t.val.1)) (x := u) hpair.continuousAt
      · simpa only [linearCollisionCoordinates, linearRatioLimit, if_neg ht] using
          (continuous_const : Continuous (fun _ : U =>
            normalizedNormRatio (base t.val.2.1 - base t.val.1) (base t.val.2.2 - base t.val.1)))

theorem tendsto_compactCoordinates_linear {i : Fin n} (c : α → Normalized i m)
    (base velocity : DoubledLabel n m → ℂ) (hr : Tendsto r l (𝓝 0))
    (hpos : ∀ᶠ x in l, 0 < r x)
    (hcoord : ∀ x v, (c x).val.doubledPoint v = base v + (r x : ℂ) * velocity v) :
    Tendsto (fun x => compactCoordinates (c x)) l (𝓝 (linearCollisionCoordinates base velocity)) := by
  have hp (x : α) (p : DoubledPair n m) :
      (c x).val.pairDifference p = (base p.val.2 - base p.val.1) +
        (r x : ℂ) * (velocity p.val.2 - velocity p.val.1) := by
    rw [pairDifference, hcoord, hcoord]
    ring
  apply Tendsto.prodMk_nhds
  · apply tendsto_pi_nhds.mpr
    intro v
    have ht := OnePoint.continuous_coe.tendsto (base (Sum.inl v)) |>.comp
      (tendsto_linear_complex hr (base (Sum.inl v)) (velocity (Sum.inl v)))
    exact ht.congr' (Eventually.of_forall fun x => congrArg ((↑) : ℂ → OnePoint ℂ)
      (hcoord x (Sum.inl v)).symm)
  · apply Tendsto.prodMk_nhds
    · apply tendsto_pi_nhds.mpr
      intro p
      simpa only [compactCoordinates, hp] using
        tendsto_linearPhaseLimit hr hpos (base p.val.2 - base p.val.1)
          (velocity p.val.2 - velocity p.val.1)
    · apply tendsto_pi_nhds.mpr
      intro t
      have heq (x : α) : (c x).val.tripleDistanceRatio t =
          normalizedNormRatio ((c x).val.pairDifference ⟨(t.val.1, t.val.2.1), t.property.1⟩)
            ((c x).val.pairDifference ⟨(t.val.1, t.val.2.2), t.property.2⟩) := rfl
      simpa only [compactCoordinates, heq, hp] using
        tendsto_linearRatioLimit hr hpos (base t.val.2.1 - base t.val.1)
          (base t.val.2.2 - base t.val.1) (velocity t.val.2.1 - velocity t.val.1)
          (velocity t.val.2.2 - velocity t.val.1)

/-- Every such actual family has the computed collision limit inside the compact closure. -/
theorem linearCollisionCoordinates_mem_compactification [NeBot l] {i : Fin n}
    (c : α → Normalized i m) (base velocity : DoubledLabel n m → ℂ)
    (hr : Tendsto r l (𝓝 0)) (hpos : ∀ᶠ x in l, 0 < r x)
    (hcoord : ∀ x v, (c x).val.doubledPoint v = base v + (r x : ℂ) * velocity v) :
    linearCollisionCoordinates base velocity ∈ compactificationSet i m := by
  apply isClosed_closure.mem_of_tendsto (tendsto_compactCoordinates_linear c base velocity hr hpos hcoord)
  exact Eventually.of_forall fun x => subset_closure ⟨c x, rfl⟩

end EnvelopingIsomorphism.Deformation.Kontsevich
