import EnvelopingIsomorphism.Deformation.Kontsevich.GraphFormsClosed

/-! Changing the normalized interior anchor, followed by the matching label swap.
The construction concerns the actual open configuration space and its raw coordinates. -/

namespace EnvelopingIsomorphism.Deformation.Kontsevich

open scoped UpperHalfPlane Topology

noncomputable section

namespace Configuration

variable {n m : ℕ}

/-- Interior relabelling by precomposition; boundary labels keep their order. -/
def relabelInterior (σ : Equiv.Perm (Fin n)) (c : Configuration n m) : Configuration n m where
  interior := c.interior ∘ σ
  boundary := c.boundary
  interior_injective := c.interior_injective.comp σ.injective
  boundary_strictMono := c.boundary_strictMono

@[simp] theorem relabelInterior_interior (σ : Equiv.Perm (Fin n)) (c : Configuration n m) (i : Fin n) :
    (relabelInterior σ c).interior i = c.interior (σ i) := rfl

@[simp] theorem relabelInterior_boundary (σ : Equiv.Perm (Fin n)) (c : Configuration n m) (i : Fin m) :
    (relabelInterior σ c).boundary i = c.boundary i := rfl

theorem relabelInterior_vertexPoint (σ : Equiv.Perm (Fin n)) (c : Configuration n m)
    (v : Fin n ⊕ Fin m) :
    (relabelInterior σ c).vertexPoint v = c.vertexPoint (Sum.map σ id v) := by
  cases v <;> rfl

theorem normalize_relabelInterior (σ : Equiv.Perm (Fin n)) (i : Fin n) (c : Configuration n m) :
    normalize i (relabelInterior σ c) = relabelInterior σ (normalize (σ i) c) := rfl

theorem normalize_normalize (i j : Fin n) (c : Configuration n m) :
    normalize i (normalize j c) = normalize i c := normalize_act i (normalizer j c) c

theorem relabelInterior_swap_twice (i j : Fin n) (c : Configuration n m) :
    relabelInterior (Equiv.swap i j) (relabelInterior (Equiv.swap i j) c) = c := by
  apply Configuration.ext
  · funext r
    simp
  · rfl

/-- First normalize at the new anchor, then swap its label with the distinguished label zero. -/
def anchorChangeNormalized (j : Fin (n + 1))
    (c : Normalized (0 : Fin (n + 1)) m) : Normalized (0 : Fin (n + 1)) m :=
  ⟨relabelInterior (Equiv.swap 0 j) (normalize j c.val), by simp⟩

theorem anchorChangeNormalized_involutive (j : Fin (n + 1)) :
    Function.Involutive (anchorChangeNormalized (m := m) j) := by
  intro c
  apply Subtype.ext
  change relabelInterior (Equiv.swap 0 j)
    (normalize j (relabelInterior (Equiv.swap 0 j) (normalize j c.val))) = c.val
  rw [normalize_relabelInterior, Equiv.swap_apply_right, relabelInterior_swap_twice,
    normalize_normalize, normalize_eq_self 0 c.val c.property]

theorem normalize_interior_complex (j i : Fin n) (c : Configuration n m) :
    ((normalize j c).interior i : ℂ) =
      ((c.interior i : ℂ) - ((c.interior j).re : ℂ)) / ((c.interior j).im : ℂ) := by
  rw [normalize, act_interior, PositiveAffine.coe_onUpper]
  simp only [normalizer, Complex.ofReal_inv, div_eq_mul_inv]
  push_cast
  ring

theorem normalize_boundary_real (j : Fin n) (i : Fin m) (c : Configuration n m) :
    (normalize j c).boundary i = (c.boundary i - (c.interior j).re) / (c.interior j).im := by
  simp only [normalize, act_boundary, PositiveAffine.onReal, normalizer, div_eq_mul_inv]
  ring

end Configuration

namespace GraphForms

variable {n m : ℕ}

/-- Explicit rational coordinate formula for changing the interior anchor. -/
def anchorChangeRaw (j : Fin (n + 1)) (x : Coordinates n m) : Coordinates n m :=
  (fun i => (interiorPoint (Equiv.swap 0 j i.succ) x - ((interiorPoint j x).re : ℂ)) /
      ((interiorPoint j x).im : ℂ),
    fun i => (x.2 i - (interiorPoint j x).re) / (interiorPoint j x).im)

@[simp] theorem anchorChangeRaw_fst (j : Fin (n + 1)) (x : Coordinates n m) (i : Fin n) :
    (anchorChangeRaw j x).1 i =
      (interiorPoint (Equiv.swap 0 j i.succ) x - ((interiorPoint j x).re : ℂ)) /
        ((interiorPoint j x).im : ℂ) := rfl

@[simp] theorem anchorChangeRaw_snd (j : Fin (n + 1)) (x : Coordinates n m) (i : Fin m) :
    (anchorChangeRaw j x).2 i = (x.2 i - (interiorPoint j x).re) / (interiorPoint j x).im := rfl

@[simp] theorem anchorChangeRaw_zero (x : Coordinates n m) : anchorChangeRaw 0 x = x := by
  apply Prod.ext
  · funext i
    simp [anchorChangeRaw]
  · funext i
    simp [anchorChangeRaw]

/-- At the selected free slot the old fixed point becomes `(I-re(z))/im(z)`. -/
theorem anchorChangeRaw_selected (i : Fin n) (x : Coordinates n m) :
    (anchorChangeRaw i.succ x).1 i = (Complex.I - ((x.1 i).re : ℂ)) / ((x.1 i).im : ℂ) := by
  simp [anchorChangeRaw]

theorem anchorChangeRaw_other (i l : Fin n) (h : l ≠ i) (x : Coordinates n m) :
    (anchorChangeRaw i.succ x).1 l = (x.1 l - ((x.1 i).re : ℂ)) / ((x.1 i).im : ℂ) := by
  have hli : l.succ ≠ i.succ := fun heq => h (Fin.succ_injective _ heq)
  simp [anchorChangeRaw, Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero l) hli]

theorem anchorChangeRaw_re (j : Fin (n + 1)) (x : Coordinates n m) (i : Fin n) :
    ((anchorChangeRaw j x).1 i).re =
      ((interiorPoint (Equiv.swap 0 j i.succ) x).re - (interiorPoint j x).re) /
        (interiorPoint j x).im := by
  simp [anchorChangeRaw]

theorem anchorChangeRaw_im (j : Fin (n + 1)) (x : Coordinates n m) (i : Fin n) :
    ((anchorChangeRaw j x).1 i).im =
      (interiorPoint (Equiv.swap 0 j i.succ) x).im / (interiorPoint j x).im := by
  simp [anchorChangeRaw]

theorem anchorChangeRaw_selected_re (i : Fin n) (x : Coordinates n m) :
    ((anchorChangeRaw i.succ x).1 i).re = -(x.1 i).re / (x.1 i).im := by
  simp

theorem anchorChangeRaw_selected_im (i : Fin n) (x : Coordinates n m) :
    ((anchorChangeRaw i.succ x).1 i).im = 1 / (x.1 i).im := by
  simp

theorem anchorChangeNormalized_coordinates (j : Fin (n + 1)) (x : CoordinateDomain n m) :
    fromNormalized (Configuration.anchorChangeNormalized j (toNormalized x)) = anchorChangeRaw j x.val := by
  apply Prod.ext
  · funext i
    change ((Configuration.normalize j (toConfiguration x)).interior (Equiv.swap 0 j i.succ) : ℂ) = _
    rw [Configuration.normalize_interior_complex]
    rfl
  · funext i
    change (Configuration.normalize j (toConfiguration x)).boundary i = _
    rw [Configuration.normalize_boundary_real]
    rfl

/-- The native normalization change, transported to the actual admissible coordinate subtype. -/
def anchorChangeDomain (j : Fin (n + 1)) (x : CoordinateDomain n m) : CoordinateDomain n m :=
  fromNormalizedDomain (Configuration.anchorChangeNormalized j (toNormalized x))

@[simp] theorem anchorChangeDomain_val (j : Fin (n + 1)) (x : CoordinateDomain n m) :
    (anchorChangeDomain j x).val = anchorChangeRaw j x.val :=
  anchorChangeNormalized_coordinates j x

theorem anchorChangeDomain_involutive (j : Fin (n + 1)) :
    Function.Involutive (anchorChangeDomain (m := m) j) := by
  intro x
  unfold anchorChangeDomain
  rw [toNormalized_fromNormalizedDomain,
    Configuration.anchorChangeNormalized_involutive, fromNormalizedDomain_toNormalized]

theorem anchorChangeRaw_admissible (j : Fin (n + 1)) {x : Coordinates n m} (hx : Admissible x) :
    Admissible (anchorChangeRaw j x) := by
  have h := (anchorChangeDomain j ⟨x, hx⟩).property
  rwa [anchorChangeDomain_val] at h

theorem anchorChangeRaw_involutive (j : Fin (n + 1)) {x : Coordinates n m} (hx : Admissible x) :
    anchorChangeRaw j (anchorChangeRaw j x) = x := by
  have h := congrArg (fun x : CoordinateDomain n m => x.val)
    (anchorChangeDomain_involutive j ⟨x, hx⟩)
  simpa only [anchorChangeDomain_val] using h

/-- The rational map is smooth wherever the chosen anchor has nonzero imaginary coordinate. -/
theorem contDiffAt_anchorChangeRaw (j : Fin (n + 1)) (x : Coordinates n m)
    (hy : (interiorPoint j x).im ≠ 0) : ContDiffAt ℝ ⊤ (anchorChangeRaw j) x := by
  have hz := (contDiff_interiorPoint (m := m) j).contDiffAt (x := x)
  have hre : ContDiffAt ℝ ⊤ (fun y : Coordinates n m => (interiorPoint j y).re) x :=
    Complex.reCLM.contDiff.contDiffAt.comp x hz
  have him : ContDiffAt ℝ ⊤ (fun y : Coordinates n m => (interiorPoint j y).im) x :=
    Complex.imCLM.contDiff.contDiffAt.comp x hz
  have hrec : ContDiffAt ℝ ⊤ (fun y : Coordinates n m => ((interiorPoint j y).re : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x hre
  have himc : ContDiffAt ℝ ⊤ (fun y : Coordinates n m => ((interiorPoint j y).im : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x him
  apply ContDiffAt.prodMk
  · apply contDiffAt_pi.mpr
    intro i
    simpa only [div_eq_mul_inv, Pi.inv_apply] using
      ((contDiff_interiorPoint (m := m) (Equiv.swap 0 j i.succ)).contDiffAt.sub hrec).mul
        (himc.inv (Complex.ofReal_ne_zero.mpr hy))
  · apply contDiffAt_pi.mpr
    intro i
    have hi : ContDiffAt ℝ ⊤ (fun y : Coordinates n m => y.2 i) x := by fun_prop
    exact (hi.sub hre).div him hy

theorem contDiffOn_anchorChangeRaw (j : Fin (n + 1)) :
    ContDiffOn ℝ ⊤ (anchorChangeRaw (m := m) j) (admissibleSet n m) := by
  intro x hx
  exact (contDiffAt_anchorChangeRaw j x (ne_of_gt (hx.interiorPoint_im_pos j))).contDiffWithinAt

theorem continuous_anchorChangeDomain (j : Fin (n + 1)) :
    Continuous (anchorChangeDomain (m := m) j) := by
  have h : Continuous (fun x : CoordinateDomain n m => (anchorChangeDomain j x).val) := by
    simp only [anchorChangeDomain_val]
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (contDiffAt_anchorChangeRaw j x.val
      (ne_of_gt (x.property.interiorPoint_im_pos j))).continuousAt.comp continuous_subtype_val.continuousAt
  exact h.subtype_mk _

/-- Genuine involutive homeomorphism of the actual open admissible coordinate domain. -/
def anchorChange (j : Fin (n + 1)) : CoordinateDomain n m ≃ₜ CoordinateDomain n m where
  toFun := anchorChangeDomain j
  invFun := anchorChangeDomain j
  left_inv := anchorChangeDomain_involutive j
  right_inv := anchorChangeDomain_involutive j
  continuous_toFun := continuous_anchorChangeDomain j
  continuous_invFun := continuous_anchorChangeDomain j

@[simp] theorem anchorChange_val (j : Fin (n + 1)) (x : CoordinateDomain n m) :
    (anchorChange j x).val = anchorChangeRaw j x.val := anchorChangeDomain_val j x

@[simp] theorem anchorChange_symm_apply (j : Fin (n + 1)) (x : CoordinateDomain n m) :
    (anchorChange j).symm x = anchorChange j x := rfl

/-- The same homeomorphism on native normalized configurations. -/
def nativeAnchorChange (j : Fin (n + 1)) :
    Configuration.Normalized (0 : Fin (n + 1)) m ≃ₜ Configuration.Normalized (0 : Fin (n + 1)) m :=
  (coordinateHomeomorph n m).symm.trans ((anchorChange j).trans (coordinateHomeomorph n m))

@[simp] theorem nativeAnchorChange_apply (j : Fin (n + 1))
    (c : Configuration.Normalized (0 : Fin (n + 1)) m) :
    nativeAnchorChange j c = Configuration.anchorChangeNormalized j c := by
  change toNormalized (anchorChangeDomain j (fromNormalizedDomain c)) = _
  simp [anchorChangeDomain]

def anchorSwapVertex (j : Fin (n + 1)) : Vertex n m → Vertex n m :=
  Sum.map (Equiv.swap 0 j) id

def anchorSwapEdge (j : Fin (n + 1)) (e : Edge n m) : Edge n m where
  source := Equiv.swap 0 j e.source
  target := anchorSwapVertex j e.target

theorem anchorChangeRaw_interior_normalized (j : Fin (n + 1))
    (x : CoordinateDomain n m) (i : Fin (n + 1)) :
    interiorPoint i (anchorChangeRaw j x.val) =
      ((Configuration.normalize j (toConfiguration x)).interior (Equiv.swap 0 j i) : ℂ) := by
  have h := interiorPoint_fromNormalized (Configuration.anchorChangeNormalized j (toNormalized x)) i
  rw [anchorChangeNormalized_coordinates] at h
  exact h

theorem anchorChangeRaw_vertex_normalized (j : Fin (n + 1))
    (x : CoordinateDomain n m) (v : Vertex n m) :
    vertexPoint v (anchorChangeRaw j x.val) =
      (Configuration.normalize j (toConfiguration x)).vertexPoint (anchorSwapVertex j v) := by
  have h := vertexPoint_fromNormalized (Configuration.anchorChangeNormalized j (toNormalized x)) v
  rw [anchorChangeNormalized_coordinates] at h
  change vertexPoint v (anchorChangeRaw j x.val) =
    (Configuration.relabelInterior (Equiv.swap 0 j) (Configuration.normalize j (toConfiguration x))).vertexPoint v at h
  rwa [Configuration.relabelInterior_vertexPoint] at h

/-- Ratio invariance is pointwise for the actual variable normalizing affine map. -/
theorem edgeRatio_anchorChangeRaw (j : Fin (n + 1)) (e : Edge n m)
    {x : Coordinates n m} (hx : Admissible x) :
    edgeRatio e (anchorChangeRaw j x) = edgeRatio (anchorSwapEdge j e) x := by
  change harmonicRatio (interiorPoint e.source (anchorChangeRaw j x))
    (vertexPoint e.target (anchorChangeRaw j x)) = _
  rw [anchorChangeRaw_interior_normalized j ⟨x, hx⟩,
    anchorChangeRaw_vertex_normalized j ⟨x, hx⟩]
  have h := Configuration.vertex_harmonicRatio_act
    (Configuration.normalizer j (toConfiguration ⟨x, hx⟩)) (toConfiguration ⟨x, hx⟩)
    (Equiv.swap 0 j e.source) (anchorSwapVertex j e.target)
  simpa only [Configuration.normalize, toConfiguration_interior, toConfiguration_vertexPoint,
    edgeRatio, edgeMap, anchorSwapEdge] using h

/-- Differentiating the ratio identity includes all derivatives of the variable affine normalizer. -/
theorem fderiv_edgeRatio_anchorChangeRaw (j : Fin (n + 1)) (e : Edge n m)
    {x : Coordinates n m} (hx : Admissible x) :
    (fderiv ℝ (edgeRatio e) (anchorChangeRaw j x)).comp (fderiv ℝ (anchorChangeRaw j) x) =
      fderiv ℝ (edgeRatio (anchorSwapEdge j e)) x := by
  have hlocal : (edgeRatio e ∘ anchorChangeRaw j) =ᶠ[𝓝 x] edgeRatio (anchorSwapEdge j e) := by
    have hAdmissible : ∀ᶠ y in 𝓝 x, Admissible y := (isOpen_admissibleSet n m).mem_nhds hx
    apply hAdmissible.mono
    intro y hy
    exact edgeRatio_anchorChangeRaw j e hy
  have h := hlocal.fderiv_eq (𝕜 := ℝ)
  rw [fderiv_comp x
    ((contDiffAt_edgeRatio e (anchorChangeRaw_admissible j hx)).differentiableAt (by simp))
    ((contDiffAt_anchorChangeRaw j x (ne_of_gt (hx.interiorPoint_im_pos j))).differentiableAt (by simp))] at h
  exact h

/-- Genuine harmonic edge-form covariance under anchor change and the corresponding label swap.
The proof uses the variable ratio identity, not constant-affine form invariance. -/
theorem edgeForm_anchorChangeRaw (j : Fin (n + 1)) (e : Edge n m)
    {x : Coordinates n m} (hx : Admissible x) :
    (edgeForm e (anchorChangeRaw j x)).compContinuousLinearMap (fderiv ℝ (anchorChangeRaw j) x) =
      edgeForm (anchorSwapEdge j e) x := by
  rw [edgeForm_eq_ratio_pullback e (anchorChangeRaw_admissible j hx),
    edgeForm_eq_ratio_pullback (anchorSwapEdge j e) hx, edgeRatio_anchorChangeRaw j e hx]
  apply ContinuousAlternatingMap.ext
  intro v
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  apply congrArg (angularForm (edgeRatio (anchorSwapEdge j e) x))
  funext i
  exact congrArg (fun f : Coordinates n m →L[ℝ] ℂ => f (v i))
    (fderiv_edgeRatio_anchorChangeRaw j e hx)

theorem edgeLinear_anchorChangeRaw (j : Fin (n + 1)) (e : Edge n m)
    {x : Coordinates n m} (hx : Admissible x) :
    (edgeLinear e (anchorChangeRaw j x)).comp (fderiv ℝ (anchorChangeRaw j) x) =
      edgeLinear (anchorSwapEdge j e) x := by
  apply ContinuousLinearMap.ext
  intro v
  rw [ContinuousLinearMap.comp_apply, edgeLinear_apply, edgeLinear_apply]
  exact congrArg (fun ω : Coordinates n m [⋀^Fin 1]→L[ℝ] ℝ => ω (fun _ => v))
    (edgeForm_anchorChangeRaw j e hx)

end GraphForms

end

end EnvelopingIsomorphism.Deformation.Kontsevich
