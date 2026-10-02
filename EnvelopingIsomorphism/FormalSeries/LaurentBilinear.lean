import EnvelopingIsomorphism.FormalSeries.Multilinear

/-! Heterogeneous bilinear Laurent extension, using the verified finite-arity convolution. -/

noncomputable section

namespace EnvelopingIsomorphism.FormalSeries.LaurentModule

universe u v
variable {k : Type u} [CommRing k]
variable {X Y Z W : Type v}
  [AddCommGroup X] [Module k X] [AddCommGroup Y] [Module k Y]
  [AddCommGroup Z] [Module k Z] [AddCommGroup W] [Module k W]

abbrev PairModule (X Y : Type v) : Fin 2 → Type v := Fin.cases X (fun _ ↦ Y)

instance pairModuleAddCommGroup (i : Fin 2) : AddCommGroup (PairModule X Y i) := by
  cases i using Fin.cases
  · change AddCommGroup X; infer_instance
  · change AddCommGroup Y; infer_instance

instance pairModuleModule (i : Fin 2) : Module k (PairModule X Y i) := by
  cases i using Fin.cases
  · change Module k X; infer_instance
  · change Module k Y; infer_instance

/-- Regard a heterogeneous bilinear map as an actual two-input multilinear map. -/
def bilinearMultilinear (f : X →ₗ[k] Y →ₗ[k] Z) : MultilinearMap k (PairModule X Y) Z :=
  LinearMap.uncurryLeft
    ((MultilinearMap.ofSubsingletonₗ k k Y Z (0 : Fin 1)).toLinearMap.comp f)

/-- Extend a heterogeneous bilinear map over the full Laurent scalar ring. -/
def extendBilinear (f : X →ₗ[k] Y →ₗ[k] Z) :
    LaurentModule k X →ₗ[LaurentSeries k] LaurentModule k Y →ₗ[LaurentSeries k] LaurentModule k Z :=
  (MultilinearMap.ofSubsingletonₗ (LaurentSeries k) (LaurentSeries k)
    (LaurentModule k Y) (LaurentModule k Z) (0 : Fin 1)).symm.toLinearMap.comp
      (extendScalars (bilinearMultilinear f)).curryLeft

theorem extendBilinear_apply (f : X →ₗ[k] Y →ₗ[k] Z)
    (x : LaurentModule k X) (y : LaurentModule k Y) :
    extendBilinear f x y = applyMultilinear (bilinearMultilinear f) (Fin.cons x (fun _ ↦ y)) := rfl

theorem coeff_extendBilinear (f : X →ₗ[k] Y →ₗ[k] Z)
    (x : LaurentModule k X) (y : LaurentModule k Y) (d : ℤ) :
    coeff (extendBilinear f x y) d =
      ∑ᶠ a : Fin 2 → ℤ, if ∑ i, a i = d then f (coeff x (a 0)) (coeff y (a 1)) else 0 := rfl

theorem boundedBelow_extendBilinear (f : X →ₗ[k] Y →ₗ[k] Z)
    (x : LaurentModule k X) (y : LaurentModule k Y) {b c : ℤ}
    (hx : BoundedBelow b x) (hy : BoundedBelow c y) :
    BoundedBelow (b + c) (extendBilinear f x y) := by
  rw [extendBilinear_apply]
  have h := boundedBelow_applyMultilinear (bilinearMultilinear f) (Fin.cons x (fun _ ↦ y))
    (b := Fin.cons b (fun _ ↦ c)) (by
      intro i
      cases i using Fin.cases
      · exact hx
      · exact hy)
  simpa only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.sum_univ_zero, add_zero] using h

theorem extendBilinear_single (f : X →ₗ[k] Y →ₗ[k] Z) (e d : ℤ) (x : X) (y : Y) :
    extendBilinear f (single e x) (single d y) = single (e + d) (f x y) := by
  rw [extendBilinear_apply]
  have h := applyMultilinear_single (bilinearMultilinear f)
    (Fin.cons e (fun _ : Fin 1 ↦ d)) (Fin.cons x (fun _ : Fin 1 ↦ y))
  have harg :
      (fun i : Fin 2 ↦ single (k := k) ((Fin.cons e (fun _ : Fin 1 ↦ d) : Fin 2 → ℤ) i)
        ((Fin.cons x (fun _ : Fin 1 ↦ y) : ∀ i, PairModule X Y i) i)) =
      (Fin.cons (single e x) (fun _ : Fin 1 ↦ single d y) :
        ∀ i, LaurentModule k (PairModule X Y i)) := by
    funext i
    cases i using Fin.cases <;> rfl
  rw [harg] at h
  convert h using 1
  · rfl
  · congr 1
    simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.sum_univ_zero, add_zero]

@[simp] theorem single_zero (e : ℤ) : single e (0 : X) = (0 : LaurentModule k X) := by
  ext d
  simp

theorem single_add (e : ℤ) (x y : X) : single e (x + y) = (single e x : LaurentModule k X) + single e y := by
  ext d
  by_cases h : d = e <;> simp [h]

theorem single_smul (e : ℤ) (c : k) (x : X) : single e (c • x) = c • (single e x : LaurentModule k X) := by
  ext d
  by_cases h : d = e <;> simp [h]

theorem boundedBelow_smul (c : k) {b : ℤ} {x : LaurentModule k X} (hx : BoundedBelow b x) :
    BoundedBelow b (c • x) := by
  intro d hd
  simp only [coeff_smul, hx d hd, smul_zero]

theorem boundedBelow_add {b : ℤ} {x y : LaurentModule k X}
    (hx : BoundedBelow b x) (hy : BoundedBelow b y) : BoundedBelow b (x + y) := by
  intro d hd
  simp only [coeff_add, hx d hd, hy d hd, add_zero]

/-- Bounded bilinear maps are determined by their values on two monomials. -/
theorem bilinear_ext_of_bounded
    (F G : LaurentModule k X →ₗ[k] LaurentModule k Y →ₗ[k] LaurentModule k Z)
    (C : ℤ)
    (hF : ∀ x y b c, BoundedBelow b x → BoundedBelow c y → BoundedBelow ((b + c) + C) (F x y))
    (hG : ∀ x y b c, BoundedBelow b x → BoundedBelow c y → BoundedBelow ((b + c) + C) (G x y))
    (hs : ∀ e d x y, F (single e x) (single d y) = G (single e x) (single d y)) : F = G := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  obtain ⟨c, hc⟩ := exists_bound y
  have ho : F.flip y = G.flip y := by
    apply linear_ext_of_bounded _ _ (c + C)
    · intro b z hz
      change BoundedBelow (b + (c + C)) (F z y)
      simpa only [add_assoc] using hF z y b c hz hc
    · intro b z hz
      change BoundedBelow (b + (c + C)) (G z y)
      simpa only [add_assoc] using hG z y b c hz hc
    · intro e v
      have hi : F (single e v) = G (single e v) := by
        apply linear_ext_of_bounded _ _ (e + C)
        · intro b z hz
          simpa only [add_comm e b, add_assoc] using hF (single e v) z e b (boundedBelow_single e v) hz
        · intro b z hz
          simpa only [add_comm e b, add_assoc] using hG (single e v) z e b (boundedBelow_single e v) hz
        · intro d w
          exact hs e d v w
      exact DFunLike.congr_fun hi y
  exact DFunLike.congr_fun ho x

theorem constant_series_smul (c : k) (x : LaurentModule k X) :
    (HahnSeries.C c : LaurentSeries k) • x = c • x :=
  HahnModule.single_zero_smul_eq_smul ℤ

theorem intCast_series_smul (n : ℤ) (x : LaurentModule k X) :
    (n : LaurentSeries k) • x = (n : k) • x := by
  rw [← HahnSeries.single_zero_intCast (Γ := ℤ) (R := k) n]
  exact HahnModule.single_zero_smul_eq_smul ℤ

/-- Restrict both scalar levels of a Laurent-bilinear map to its coefficient ring. -/
def restrictBilinear
    (F : LaurentModule k X →ₗ[LaurentSeries k] LaurentModule k Y →ₗ[LaurentSeries k] LaurentModule k Z) :
    LaurentModule k X →ₗ[k] LaurentModule k Y →ₗ[k] LaurentModule k Z where
  toFun x := (F x).restrictScalars k
  map_add' x y := by
    apply LinearMap.ext
    intro z
    exact DFunLike.congr_fun (F.map_add x y) z
  map_smul' c x := by
    apply LinearMap.ext
    intro y
    change F (c • x) y = c • F x y
    have h := DFunLike.congr_fun (F.map_smul (HahnSeries.C c) x) y
    change F ((HahnSeries.C c : LaurentSeries k) • x) y = (HahnSeries.C c : LaurentSeries k) • F x y at h
    simpa only [constant_series_smul] using h

@[simp] theorem restrictBilinear_apply
    (F : LaurentModule k X →ₗ[LaurentSeries k] LaurentModule k Y →ₗ[LaurentSeries k] LaurentModule k Z)
    (x : LaurentModule k X) (y : LaurentModule k Y) : restrictBilinear F x y = F x y := rfl

/-- Bounded trilinear maps are determined by their values on monomial triples. -/
theorem trilinear_ext_of_bounded
    (F G : LaurentModule k X →ₗ[k] LaurentModule k Y →ₗ[k] LaurentModule k Z →ₗ[k] LaurentModule k W)
    (C : ℤ)
    (hF : ∀ x y z b c d, BoundedBelow b x → BoundedBelow c y → BoundedBelow d z →
      BoundedBelow (((b + c) + d) + C) (F x y z))
    (hG : ∀ x y z b c d, BoundedBelow b x → BoundedBelow c y → BoundedBelow d z →
      BoundedBelow (((b + c) + d) + C) (G x y z))
    (hs : ∀ b c d x y z, F (single b x) (single c y) (single d z) =
      G (single b x) (single c y) (single d z)) : F = G := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  apply LinearMap.ext
  intro z
  obtain ⟨d, hd⟩ := exists_bound z
  let ev : (LaurentModule k Z →ₗ[k] LaurentModule k W) →ₗ[k] LaurentModule k W := LinearMap.applyₗ z
  have ho : F.compr₂ ev = G.compr₂ ev := by
    apply bilinear_ext_of_bounded _ _ (d + C)
    · intro x y b c hx hy
      change BoundedBelow ((b + c) + (d + C)) (F x y z)
      simpa only [add_assoc] using hF x y z b c d hx hy hd
    · intro x y b c hx hy
      change BoundedBelow ((b + c) + (d + C)) (G x y z)
      simpa only [add_assoc] using hG x y z b c d hx hy hd
    · intro b c v w
      have hi : F (single b v) (single c w) = G (single b v) (single c w) := by
        apply linear_ext_of_bounded _ _ ((b + c) + C)
        · intro e z hz
          simpa only [add_comm (b + c) e, add_assoc] using
            hF (single b v) (single c w) z b c e (boundedBelow_single b v) (boundedBelow_single c w) hz
        · intro e z hz
          simpa only [add_comm (b + c) e, add_assoc] using
            hG (single b v) (single c w) z b c e (boundedBelow_single b v) (boundedBelow_single c w) hz
        · intro e u
          exact hs b c e v w u
      exact DFunLike.congr_fun hi z
  exact DFunLike.congr_fun (DFunLike.congr_fun ho x) y

section Operations

variable {T : Type v} [AddCommGroup T] [Module k T]

/-- Nest a bilinear operation in the right argument of another one. -/
def nestRight (f : X →ₗ[k] W →ₗ[k] T) (g : Y →ₗ[k] Z →ₗ[k] W) :
    X →ₗ[k] Y →ₗ[k] Z →ₗ[k] T where
  toFun x := g.compr₂ (f x)
  map_add' x y := by ext z w; simp
  map_smul' c x := by ext y z; simp

@[simp] theorem nestRight_apply (f : X →ₗ[k] W →ₗ[k] T) (g : Y →ₗ[k] Z →ₗ[k] W)
    (x : X) (y : Y) (z : Z) : nestRight f g x y z = f x (g y z) := rfl

/-- Postcompose a curried trilinear map with a linear map. -/
def postTrilinear (f : X →ₗ[k] Y →ₗ[k] Z →ₗ[k] W) (g : W →ₗ[k] T) :
    X →ₗ[k] Y →ₗ[k] Z →ₗ[k] T :=
  f.compr₂ (LinearMap.llcomp k Z W T g)

@[simp] theorem postTrilinear_apply (f : X →ₗ[k] Y →ₗ[k] Z →ₗ[k] W) (g : W →ₗ[k] T)
    (x : X) (y : Y) (z : Z) : postTrilinear f g x y z = g (f x y z) := rfl

end Operations

end EnvelopingIsomorphism.FormalSeries.LaurentModule
