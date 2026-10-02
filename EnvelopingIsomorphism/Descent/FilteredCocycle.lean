import EnvelopingIsomorphism.Descent.AdditiveCocycle
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Tactic.Group

/-!
Finite elimination of a noncommutative cocycle by linear corrections.
The linear correction lemma only asks for logarithms and exponentials to agree
in one additive filtration layer.  Neither BCH nor an inverse relation between
logarithms and exponentials is used.
-/

namespace EnvelopingIsomorphism.Descent

open scoped BigOperators

universe u v w z

variable {Γ : Type u} [Group Γ]
variable {G : Type v} [Group G]

/-- A cocycle for an action by group automorphisms. -/
def IsGroupCocycle (ρ : Γ →* MulAut G) (a : Γ → G) : Prop :=
  ∀ σ τ, a (σ * τ) = a σ * ρ σ (a τ)

/-- Change a cocycle by a constant gauge transformation. -/
def cocycleGauge (ρ : Γ →* MulAut G) (b : G) (a : Γ → G) : Γ → G :=
  fun σ => b * a σ * (ρ σ b)⁻¹

@[simp] theorem cocycleGauge_one (ρ : Γ →* MulAut G) (a : Γ → G) :
    cocycleGauge ρ 1 a = a := by
  funext σ
  simp [cocycleGauge]

theorem IsGroupCocycle.gauge {ρ : Γ →* MulAut G} {a : Γ → G}
    (ha : IsGroupCocycle ρ a) (b : G) : IsGroupCocycle ρ (cocycleGauge ρ b a) := by
  intro σ τ
  simp only [cocycleGauge, ha σ τ, map_mul, MulAut.mul_apply, map_inv]
  group

@[simp] theorem cocycleGauge_comp (ρ : Γ →* MulAut G) (b c : G) (a : Γ → G) :
    cocycleGauge ρ b (cocycleGauge ρ c a) = cocycleGauge ρ (b * c) a := by
  funext σ
  simp [cocycleGauge, mul_assoc]

theorem cocycleGauge_eq_one_iff (ρ : Γ →* MulAut G) (b : G) (a : Γ → G) (σ : Γ) :
    cocycleGauge ρ b a σ = 1 ↔ a σ = b⁻¹ * ρ σ b := by
  simp only [cocycleGauge]
  constructor
  · intro h
    have h' := congrArg (fun x => b⁻¹ * x * ρ σ b) h
    simpa [mul_assoc] using h'
  · intro h
    simp [h]

/-- Finite induction on a subgroup filtration.  The subsequent linear-correction
lemma constructs the step assumed here from first-order exp/log data. -/
theorem exists_coboundary_of_filtration
    (ρ : Γ →* MulAut G) (F : ℕ → Subgroup G) (n : ℕ)
    (hmono : Antitone F) (hfinal : F n = ⊥)
    (hstep : ∀ i < n, ∀ a : Γ → G, IsGroupCocycle ρ a →
      (∀ σ, a σ ∈ F i) →
      ∃ c ∈ F i, ∀ σ, cocycleGauge ρ c a σ ∈ F (i + 1))
    (a : Γ → G) (ha : IsGroupCocycle ρ a) (hmem : ∀ σ, a σ ∈ F 0) :
    ∃ b ∈ F 0, ∀ σ, a σ = b⁻¹ * ρ σ b := by
  induction n generalizing F a with
  | zero =>
      refine ⟨1, (F 0).one_mem, fun σ => ?_⟩
      have h := hmem σ
      rw [hfinal] at h
      simpa using h
  | succ n ih =>
      obtain ⟨c, hc, hac⟩ := hstep 0 (Nat.zero_lt_succ n) a ha hmem
      have hshift : Antitone (fun i => F (i + 1)) :=
        fun i j hij => hmono (Nat.add_le_add_right hij 1)
      have hshiftStep : ∀ i < n, ∀ a : Γ → G, IsGroupCocycle ρ a →
          (∀ σ, a σ ∈ F (i + 1)) →
          ∃ d ∈ F (i + 1), ∀ σ, cocycleGauge ρ d a σ ∈ F ((i + 1) + 1) := by
        intro i hi a ha hmem
        exact hstep (i + 1) (Nat.add_lt_add_right hi 1) a ha hmem
      obtain ⟨b, hb, hab⟩ := ih (fun i => F (i + 1)) hshift hfinal hshiftStep
        (cocycleGauge ρ c a) (ha.gauge c) hac
      refine ⟨b * c, (F 0).mul_mem (hmono (Nat.zero_le 1) hb) hc, fun σ => ?_⟩
      apply (cocycleGauge_eq_one_iff ρ (b * c) a σ).mp
      rw [← cocycleGauge_comp]
      exact (cocycleGauge_eq_one_iff ρ b (cocycleGauge ρ c a) σ).mpr (hab σ)

section LinearCorrection

variable {W : Type w} [AddCommGroup W] [Module ℚ W]
variable {D : Type z} [AddCommGroup D] [Module ℚ D]

/-- An additive first-order observation of a subgroup, equivariant for the given
action, with zero observation forcing membership in the next subgroup. -/
structure FirstOrderLayer (ρ : Γ →* MulAut G) (H N : Subgroup G)
    (τ : Γ →* Module.End ℚ W) where
  observe : G → W
  stable : ∀ σ g, g ∈ H → ρ σ g ∈ H
  observe_mul : ∀ g ∈ H, ∀ h ∈ H, observe (g * h) = observe g + observe h
  observe_action : ∀ σ g, g ∈ H → observe (ρ σ g) = τ σ (observe g)
  mem_next : ∀ g ∈ H, observe g = 0 → g ∈ N

namespace FirstOrderLayer

variable {ρ : Γ →* MulAut G} {H N : Subgroup G} {τ : Γ →* Module.End ℚ W}
variable (layer : FirstOrderLayer ρ H N τ)

@[simp] theorem observe_one : layer.observe 1 = 0 := by
  have h := layer.observe_mul 1 H.one_mem 1 H.one_mem
  simp only [one_mul] at h
  exact (add_left_cancel (show layer.observe 1 + layer.observe 1 =
    layer.observe 1 + 0 by simpa using h.symm))

theorem observe_inv (g : G) (hg : g ∈ H) : layer.observe g⁻¹ = -layer.observe g := by
  have h := layer.observe_mul g hg g⁻¹ (H.inv_mem hg)
  rw [mul_inv_cancel, layer.observe_one] at h
  exact eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using h.symm)

/-- A linear correction removes one filtration layer.  The maps `logarithm` and
`exponential` need only agree with `linearPart` after observation; they need not
be inverse, and no group action on their vector space is required. -/
theorem correct_cocycle [Fintype Γ]
    (linearPart : D →ₗ[ℚ] W) (logarithm : G → D) (exponential : D → G)
    (hlog : ∀ g ∈ H, linearPart (logarithm g) = layer.observe g)
    (hexp_mem : ∀ d, exponential d ∈ H)
    (hexp : ∀ d, layer.observe (exponential d) = linearPart d)
    (a : Γ → G) (ha : IsGroupCocycle ρ a) (hmem : ∀ σ, a σ ∈ H) :
    ∃ c ∈ H, ∀ σ, cocycleGauge ρ c a σ ∈ N := by
  classical
  let v : D := cocycleAverage (fun σ => logarithm (a σ))
  have hv : linearPart v = cocycleAverage (fun σ => layer.observe (a σ)) := by
    simp only [v, cocycleAverage, map_smul, map_sum]
    congr 1
    exact Finset.sum_congr rfl fun σ _ => hlog (a σ) (hmem σ)
  have hobs : ∀ σ τ', layer.observe (a (σ * τ')) =
      layer.observe (a σ) + τ σ (layer.observe (a τ')) := by
    intro σ τ'
    rw [ha σ τ', layer.observe_mul _ (hmem σ) _ (layer.stable σ _ (hmem τ')),
      layer.observe_action σ _ (hmem τ')]
  refine ⟨exponential (-v), hexp_mem (-v), fun σ => ?_⟩
  apply layer.mem_next
  · exact H.mul_mem (H.mul_mem (hexp_mem (-v)) (hmem σ))
      (H.inv_mem (layer.stable σ _ (hexp_mem (-v))))
  · simp only [cocycleGauge]
    rw [layer.observe_mul _ (H.mul_mem (hexp_mem (-v)) (hmem σ)) _
        (H.inv_mem (layer.stable σ _ (hexp_mem (-v)))),
      layer.observe_mul _ (hexp_mem (-v)) _ (hmem σ),
      layer.observe_inv _ (layer.stable σ _ (hexp_mem (-v))),
      layer.observe_action σ _ (hexp_mem (-v)), hexp, map_neg, hv]
    rw [additive_cocycle_average τ (fun σ => layer.observe (a σ)) hobs σ, map_neg]
    abel

end FirstOrderLayer

end LinearCorrection

/-- Explicit finite linear-correction data imply triviality of every cocycle in
the first subgroup.  This combines averaging with finite induction and has no
cohomological triviality or correction-step hypothesis. -/
theorem exists_coboundary_of_linear_corrections [Fintype Γ]
    (ρ : Γ →* MulAut G) (F : ℕ → Subgroup G) (n : ℕ)
    (hmono : Antitone F) (hfinal : F n = ⊥)
    (W : ℕ → Type w) [∀ i, AddCommGroup (W i)] [∀ i, Module ℚ (W i)]
    (D : ℕ → Type z) [∀ i, AddCommGroup (D i)] [∀ i, Module ℚ (D i)]
    (τ : ∀ i, Γ →* Module.End ℚ (W i))
    (layer : ∀ i, FirstOrderLayer ρ (F i) (F (i + 1)) (τ i))
    (linearPart : ∀ i, D i →ₗ[ℚ] W i)
    (logarithm : ∀ i, G → D i) (exponential : ∀ i, D i → G)
    (hlog : ∀ i < n, ∀ g ∈ F i,
      linearPart i (logarithm i g) = (layer i).observe g)
    (hexp_mem : ∀ i < n, ∀ d, exponential i d ∈ F i)
    (hexp : ∀ i < n, ∀ d,
      (layer i).observe (exponential i d) = linearPart i d)
    (a : Γ → G) (ha : IsGroupCocycle ρ a) (hmem : ∀ σ, a σ ∈ F 0) :
    ∃ b ∈ F 0, ∀ σ, a σ = b⁻¹ * ρ σ b := by
  apply exists_coboundary_of_filtration ρ F n hmono hfinal ?_ a ha hmem
  intro i hi a ha hmem
  exact (layer i).correct_cocycle (linearPart i) (logarithm i) (exponential i)
    (hlog i hi) (hexp_mem i hi) (hexp i hi) a ha hmem

/-- The final torsor computation: a coboundary corrects a twisted fixed point
into a fixed point.  An application to matrices then descends their entries. -/
theorem corrected_point_fixed
    {X : Type w} [MulAction G X] [MulAction Γ X]
    (ρ : Γ →* MulAut G)
    (compatible : ∀ (σ : Γ) (g : G) (x : X), σ • (g • x) = ρ σ g • (σ • x))
    (a : Γ → G) (x : X)
    (hx : ∀ σ, σ • x = (a σ)⁻¹ • x)
    (b : G) (hb : ∀ σ, a σ = b⁻¹ * ρ σ b) :
    ∀ (σ : Γ), σ • (b • x) = b • x := by
  intro σ
  rw [compatible, hx σ, ← mul_smul, hb σ]
  simp

end EnvelopingIsomorphism.Descent
