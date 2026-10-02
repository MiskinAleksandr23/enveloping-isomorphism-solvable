import Mathlib.Algebra.Lie.Nilpotent

namespace EnvelopingIsomorphism.Lie

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

/-- A nilpotent ideal acts nilpotently on its ambient Lie algebra. -/
theorem isNilpotent_ideal_action (I : LieIdeal R L) [LieRing.IsNilpotent I] :
    LieModule.IsNilpotent I L := by
  let K : LieSubmodule R I L := I.toLieSubalgebra.toLieSubmodule
  have hK : LieModule.IsNilpotent I K := by
    change LieModule.IsNilpotent I I
    infer_instance
  obtain ⟨n, hn⟩ := K.isNilpotent_iff_exists_lcs_eq_bot.mp hK
  have hfirst : LieModule.lowerCentralSeries R I L 1 ≤ K := by
    rw [LieModule.lowerCentralSeries_succ, LieModule.lowerCentralSeries_zero]
    apply (LieSubmodule.lie_le_iff _ _ _).mpr
    intro x hx y hy
    change ⁅(x : L), y⁆ ∈ I
    exact lie_mem_left R L I x y x.property
  have hbound (m : ℕ) : LieModule.lowerCentralSeries R I L (m + 1) ≤ K.lcs m := by
    induction m with
    | zero => simpa using hfirst
    | succ m ih =>
      rw [LieModule.lowerCentralSeries_succ, LieSubmodule.lcs_succ]
      exact LieSubmodule.mono_lie_right ⊤ ih
  exact LieModule.IsNilpotent.mk L (le_bot_iff.mp (hn ▸ hbound n))

/-- Nilpotence of the action on the ambient algebra detects nilpotence of an ideal. -/
theorem isNilpotent_of_ideal_action (I : LieIdeal R L) [LieModule.IsNilpotent I L] :
    LieRing.IsNilpotent I := by
  let f : I →ₗ⁅R⁆ I := LieHom.id
  let g : I →ₗ[R] L := I.incl.toLinearMap
  have hfg : ∀ x m, ⁅f x, g m⁆ = g ⁅x, m⁆ := fun _ _ => rfl
  exact (show Function.Injective g from Subtype.coe_injective).lieModuleIsNilpotent hfg

/-- An ideal is nilpotent exactly when its action on the ambient algebra is nilpotent. -/
theorem isNilpotent_ideal_iff_action (I : LieIdeal R L) :
    LieRing.IsNilpotent I ↔ LieModule.IsNilpotent I L := by
  constructor
  · intro h
    letI := h
    exact isNilpotent_ideal_action I
  · intro h
    letI := h
    exact isNilpotent_of_ideal_action I

/-- Intrinsic nilpotence of an ideal can be computed by its lower central series in `L`. -/
theorem isNilpotent_ideal_iff_lcs_eq_bot (I : LieIdeal R L) :
    LieRing.IsNilpotent I ↔ ∃ n, I.lcs L n = ⊥ := by
  rw [isNilpotent_ideal_iff_action, LieModule.isNilpotent_iff R]
  refine exists_congr fun n => ?_
  simp only [← LieSubmodule.toSubmodule_inj, I.coe_lcs_eq, LieSubmodule.bot_toSubmodule]

end EnvelopingIsomorphism.Lie
