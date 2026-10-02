import EnvelopingIsomorphism.Deformation.Kontsevich.MarkedDRIdentification

/-! The genuine compact full direction/ratio closure of normalized injective
planar arrays. Its coefficients retain every pair direction and triple ratio. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Kontsevich.PlanarClusterCompactification

open ForestDirectionRatioCoordinates MarkedDRIdentification Topology Set
open scoped Classical

variable {q : ℕ} (a b : Fin q)

abbrev Normalized := {z : Fin q → ℂ // Function.Injective z ∧ z a = 0 ∧ ‖z b‖ = 1}

def encode (z : Normalized a b) : Data (Fin q) := ofPositions z.val

theorem reference_ne (z : Normalized a b) : a ≠ b := by
  intro h
  have hn := z.property.2.2
  have hz : z.val b = 0 := (congrArg z.val h).symm.trans z.property.2.1
  rw [hz, norm_zero] at hn
  exact zero_ne_one hn

theorem continuous_encode : Continuous (encode a b) := by
  have happ (j : Fin q) : Continuous (fun z : Normalized a b => z.val j) :=
    (continuous_apply j).comp continuous_subtype_val
  apply Continuous.prodMk
  · apply continuous_pi
    intro p
    apply continuous_iff_continuousAt.mpr
    intro z
    exact (continuousAt_complexPhase (sub_ne_zero.mpr (z.property.1.ne p.property.symm))).comp
      (f := fun w : Normalized a b => w.val p.val.2 - w.val p.val.1) (x := z)
      ((happ p.val.2).sub (happ p.val.1)).continuousAt
  · apply continuous_pi
    intro t
    apply continuous_iff_continuousAt.mpr
    intro z
    have hc : Continuous (fun z : Normalized a b =>
        (z.val t.val.2.1 - z.val t.val.1, z.val t.val.2.2 - z.val t.val.1)) :=
      ((happ t.val.2.1).sub (happ t.val.1)).prodMk ((happ t.val.2.2).sub (happ t.val.1))
    exact (continuousAt_normalizedNormRatio _ _
      (fun h => (sub_ne_zero.mpr (z.property.1.ne t.property.1.symm)) h.1)).comp
        (f := fun z : Normalized a b => (z.val t.val.2.1 - z.val t.val.1, z.val t.val.2.2 - z.val t.val.1))
        (x := z) hc.continuousAt

theorem recover_encode (hab : a ≠ b) (z : Normalized a b) (j : Fin q) :
    recoverArray a b hab (encode a b z) j = z.val j := by
  rw [encode, recoverArray_ofPositions z.val a b hab (z.property.1.ne hab), z.property.2.1,
    sub_zero, sub_zero, z.property.2.2, Complex.ofReal_one, div_one]

theorem encode_injective : Function.Injective (encode a b) := by
  intro z w h
  apply Subtype.ext
  funext j
  rw [← recover_encode a b (reference_ne a b z) z j,
    ← recover_encode a b (reference_ne a b z) w j, h]

theorem encode_mem_finiteRegion (hab : a ≠ b) (z : Normalized a b) :
    encode a b z ∈ MarkedDRIdentification.FiniteRegion Finset.univ a b hab :=
  ofPositions_mem_finiteRegion _ z.val a b hab (z.property.1.ne hab)

/-- Distinct chosen marks give an actual nonempty normalized planar space. -/
theorem nonempty_normalized (hab : a ≠ b) : Nonempty (Normalized a b) := by
  let p : Fin q → ℂ := fun j => (j.val : ℂ)
  have hp : Function.Injective p := by
    intro i j h
    apply Fin.ext
    change (i.val : ℂ) = (j.val : ℂ) at h
    exact_mod_cast h
  let R : ℝ := ‖p b - p a‖
  have hR : 0 < R := norm_pos_iff.mpr (sub_ne_zero.mpr (hp.ne hab.symm))
  have hRC : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
  refine ⟨⟨fun j => (p j - p a) / (R : ℂ), ?_, ?_, ?_⟩⟩
  · intro i j h
    apply hp
    have h' := congrArg (fun z : ℂ => z * (R : ℂ)) h
    rw [div_mul_cancel₀ _ hRC, div_mul_cancel₀ _ hRC] at h'
    exact sub_left_inj.mp h'
  · simp
  · rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hR.le]
    exact div_self hR.ne'

/-- Actual closure inside the finite product of compact direction/ratio coordinates. -/
def carrier : Set (Data (Fin q)) := closure (range (encode a b))

abbrev Space := carrier a b

instance : CompactSpace (Space a b) := isCompact_iff_compactSpace.mp isClosed_closure.isCompact

instance : T2Space (Space a b) := inferInstanceAs (T2Space (carrier a b))

def embedding (z : Normalized a b) : Space a b := ⟨encode a b z, subset_closure ⟨z, rfl⟩⟩

theorem continuous_embedding : Continuous (embedding a b) := (continuous_encode a b).subtype_mk _

theorem embedding_injective : Function.Injective (embedding a b) :=
  fun _ _ h => encode_injective a b (congrArg Subtype.val h)

theorem denseRange_embedding : DenseRange (embedding a b) := by
  exact ((denseRange_inclusion_iff subset_closure).mpr (Subset.rfl)).comp
    Set.rangeFactorization_surjective.denseRange (continuous_inclusion subset_closure)

end EnvelopingIsomorphism.Deformation.Kontsevich.PlanarClusterCompactification
