import EnvelopingIsomorphism.Deformation.Gauge.LinearObstruction

/-! Only the degree-zero and degree-one tangent maps are needed for gauge
reflection. The required lifting statement is exactness at the middle of one
explicit three-term sequence, and follows from a full quasi-isomorphism when
one is available. -/

namespace EnvelopingIsomorphism.Deformation.Gauge

open CategoryTheory

universe u v
variable {k : Type u} [Ring k]
variable (C D : CochainComplex (ModuleCat.{v} k) ℤ)

/-- The two tangent components and their single chain identity. -/
structure LowTangent where
  zero : C.X 0 →ₗ[k] D.X 0
  one : C.X 1 →ₗ[k] D.X 1
  comm : (D.d 0 1).hom.comp zero = one.comp (C.d 0 1).hom

namespace LowTangent

variable {C D}

def ofChainMap (φ : C ⟶ D) : LowTangent C D where
  zero := (φ.f 0).hom
  one := (φ.f 1).hom
  comm := by
    have h := congrArg ModuleCat.Hom.hom (φ.comm 0 1)
    exact h

/-- The pair (source correction, target boundary) maps to the displacement/error. -/
def left (F : LowTangent C D) :
    (C.X 0 × D.X (-1)) →ₗ[k] (C.X 1 × D.X 0) where
  toFun z := (-C.d 0 1 z.1, F.zero z.1 + D.d (-1) 0 z.2)
  map_add' a b := by
    ext <;> simp only [Prod.fst_add, Prod.snd_add, map_add, neg_add_rev] <;> abel
  map_smul' a b := by
    ext <;> simp only [Prod.smul_fst, Prod.smul_snd, map_smul, smul_add, smul_neg,
      RingHom.id_apply]

/-- Closedness and compatibility of the source displacement with the target error. -/
def right (F : LowTangent C D) :
    (C.X 1 × D.X 0) →ₗ[k] (C.X 2 × D.X 1) where
  toFun z := (C.d 1 2 z.1, F.one z.1 + D.d 0 1 z.2)
  map_add' a b := by
    ext <;> simp only [Prod.fst_add, Prod.snd_add, map_add]
    abel
  map_smul' a b := by
    ext <;> simp only [Prod.smul_fst, Prod.smul_snd, map_smul, smul_add, RingHom.id_apply]

@[simp] theorem left_apply (F : LowTangent C D) (y : C.X 0) (u : D.X (-1)) :
    F.left (y, u) = (-C.d 0 1 y, F.zero y + D.d (-1) 0 u) := rfl

@[simp] theorem right_apply (F : LowTangent C D) (δ : C.X 1) (x : D.X 0) :
    F.right (δ, x) = (C.d 1 2 δ, F.one δ + D.d 0 1 x) := rfl

theorem right_left (F : LowTangent C D) (z : C.X 0 × D.X (-1)) :
    F.right (F.left z) = 0 := by
  have hC : C.d 1 2 (C.d 0 1 z.1) = 0 := by
    have h := congrArg (fun f : C.X 0 ⟶ C.X 2 => f z.1) (C.d_comp_d 0 1 2)
    exact h
  have hD : D.d 0 1 (D.d (-1) 0 z.2) = 0 := by
    have h := congrArg (fun f : D.X (-1) ⟶ D.X 1 => f z.2) (D.d_comp_d (-1) 0 1)
    exact h
  have hc : D.d 0 1 (F.zero z.1) = F.one (C.d 0 1 z.1) :=
    LinearMap.congr_fun F.comm z.1
  ext
  · change C.d 1 2 (-C.d 0 1 z.1) = 0
    rw [map_neg, hC, neg_zero]
  · change F.one (-C.d 0 1 z.1) + D.d 0 1 (F.zero z.1 + D.d (-1) 0 z.2) = 0
    rw [map_neg, map_add, hc, hD, add_zero, neg_add_cancel]

/-- Ordinary linear exactness, with no gauge-reflection conclusion in its definition. -/
class IsMiddleExact (F : LowTangent C D) : Prop where
  range_eq_ker : LinearMap.range F.left = LinearMap.ker F.right

theorem remove_obstruction (F : LowTangent C D) [F.IsMiddleExact]
    (δ : C.X 1) (hδ : C.d 1 2 δ = 0) (x : D.X 0)
    (hx : F.one δ = -D.d 0 1 x) :
    ∃ y : C.X 0, ∃ u : D.X (-1),
      C.d 0 1 y = -δ ∧ x = F.zero y + D.d (-1) 0 u := by
  have h : (δ, x) ∈ LinearMap.range F.left := by
    rw [IsMiddleExact.range_eq_ker]
    change F.right (δ, x) = 0
    rw [right_apply, hδ, hx, neg_add_cancel]
    rfl
  obtain ⟨⟨y, u⟩, he⟩ := h
  have hy := congrArg Prod.fst he
  have hu := congrArg Prod.snd he
  refine ⟨y, u, ?_, hu.symm⟩
  change -C.d 0 1 y = δ at hy
  exact neg_eq_iff_eq_neg.mp hy

/-- The familiar full quasi-isomorphism hypothesis proves the weaker exactness. -/
instance ofChainMap_isMiddleExact (φ : C ⟶ D) [QuasiIso φ] :
    (ofChainMap φ).IsMiddleExact where
  range_eq_ker := by
    apply le_antisymm
    · rintro z ⟨w, rfl⟩
      exact right_left _ w
    · intro z hz
      change (ofChainMap φ).right z = 0 at hz
      have hδ : C.d 1 2 z.1 = 0 := congrArg Prod.fst hz
      have hx : φ.f 1 z.1 = -D.d 0 1 z.2 := by
        have h := congrArg Prod.snd hz
        exact eq_neg_of_add_eq_zero_left h
      obtain ⟨y, u, hy, hu⟩ := remove_linear_obstruction φ z.1 hδ z.2 hx
      refine ⟨(y, u), ?_⟩
      ext
      · change -C.d 0 1 y = z.1
        rw [hy, neg_neg]
      · exact hu.symm

end LowTangent

end EnvelopingIsomorphism.Deformation.Gauge
