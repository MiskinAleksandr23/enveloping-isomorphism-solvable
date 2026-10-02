import EnvelopingIsomorphism.FormalSeries.Endomorphism
import Mathlib.RingTheory.HahnSeries.PowerSeries

/-! A formal series of endomorphisms acts on vector-valued power series by
convolution. Associativity is inherited from mathlib's Hahn module action. -/

noncomputable section

namespace EnvelopingIsomorphism.FormalSeries.EndomorphismSeries

open PowerSeries

variable {k A : Type*} [CommRing k] [Ring A] [Algebra k A]

private abbrev HModule := HahnModule ℕ (Module.End k A) A

/-- The additive identification with the Hahn module indexed by natural numbers. -/
def moduleEquiv : PowerSeries A ≃+ HModule (k := k) (A := A) where
  toEquiv := HahnSeries.toPowerSeries.symm.toEquiv.trans (HahnModule.of (Module.End k A))
  map_add' p q := by
    change HahnModule.of (Module.End k A) (HahnSeries.toPowerSeries.symm (p + q)) = _
    rw [map_add]
    rfl

/-- Convolution action of an endomorphism series on an algebra-valued series. -/
def act (F : PowerSeries (Module.End k A)) (p : PowerSeries A) : PowerSeries A :=
  (moduleEquiv (k := k)).symm
    (HahnSeries.toPowerSeries.symm F • moduleEquiv (k := k) p)

theorem coeff_act (F : PowerSeries (Module.End k A)) (p : PowerSeries A) (n : ℕ) :
    coeff n (act F p) =
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
        (coeff ij.1 F) (coeff ij.2 p) := by
  have hc (z : HModule (k := k) (A := A)) :
      coeff n ((moduleEquiv (k := k)).symm z) =
        ((HahnModule.of (Module.End k A)).symm z).coeff n :=
    HahnSeries.coeff_toPowerSeries
  rw [act, hc, HahnModule.coeff_smul]
  classical
  refine (Finset.sum_filter_ne_zero _).symm.trans
    ((Finset.sum_congr ?_ fun _ _ ↦ rfl).trans (Finset.sum_filter_ne_zero _))
  ext ij
  simp only [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal,
    Finset.mem_vaddAntidiagonal, HahnSeries.mem_support,
    HahnSeries.coeff_toPowerSeries_symm, moduleEquiv, AddEquiv.coe_mk,
    Equiv.coe_trans, RingEquiv.toEquiv_eq_coe, RingEquiv.coe_toEquiv,
    vadd_eq_add]
  change ((coeff ij.1 F ≠ 0 ∧ coeff ij.2 p ≠ 0 ∧ ij.1 + ij.2 = n) ∧
    (coeff ij.1 F) (coeff ij.2 p) ≠ 0) ↔
    (ij.1 + ij.2 = n ∧ (coeff ij.1 F) (coeff ij.2 p) ≠ 0)
  constructor
  · exact fun h ↦ ⟨h.1.2.2, h.2⟩
  · intro h
    refine ⟨⟨?_, ?_, h.1⟩, h.2⟩
    · intro hz
      exact h.2 (by rw [hz]; rfl)
    · intro hz
      exact h.2 (by rw [hz, map_zero])

@[simp] theorem act_one (p : PowerSeries A) : act (1 : PowerSeries (Module.End k A)) p = p := by
  simp [act]

theorem act_mul (F G : PowerSeries (Module.End k A)) (p : PowerSeries A) :
    act (F * G) p = act F (act G p) := by
  simp [act, map_mul, mul_smul]

@[simp] theorem act_zero_left (p : PowerSeries A) : act (0 : PowerSeries (Module.End k A)) p = 0 := by
  simp [act]

@[simp] theorem act_zero_right (F : PowerSeries (Module.End k A)) : act F 0 = 0 := by
  simp [act]

theorem act_add_left (F G : PowerSeries (Module.End k A)) (p : PowerSeries A) :
    act (F + G) p = act F p + act G p := by
  simp [act, add_smul]

theorem act_add_right (F : PowerSeries (Module.End k A)) (p q : PowerSeries A) :
    act F (p + q) = act F p + act F q := by
  simp [act, smul_add]

theorem act_smul_right (F : PowerSeries (Module.End k A)) (r : k) (p : PowerSeries A) :
    act F (r • p) = r • act F p := by
  ext n
  simp only [coeff_act, PowerSeries.coeff_smul, map_smul, Finset.smul_sum]

/-- Formal operator series act by linear endomorphisms, and composition of
their actions is multiplication of the operator series. -/
def actionHom : PowerSeries (Module.End k A) →+* Module.End k (PowerSeries A) where
  toFun F :=
    { toFun := act F
      map_add' := act_add_right F
      map_smul' := act_smul_right F }
  map_one' := by apply LinearMap.ext; intro p; exact act_one (k := k) p
  map_mul' F G := by apply LinearMap.ext; intro p; exact act_mul F G p
  map_zero' := by apply LinearMap.ext; intro p; exact act_zero_left (k := k) p
  map_add' F G := by apply LinearMap.ext; intro p; exact act_add_left F G p

@[simp] theorem actionHom_apply (F : PowerSeries (Module.End k A)) (p : PowerSeries A) :
    actionHom F p = act F p := rfl

end EnvelopingIsomorphism.FormalSeries.EndomorphismSeries
