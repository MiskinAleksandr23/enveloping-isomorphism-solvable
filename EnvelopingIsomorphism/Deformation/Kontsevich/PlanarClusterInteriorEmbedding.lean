import EnvelopingIsomorphism.Deformation.Kontsevich.PlanarClusterDoubledData

/-! The compact planar cluster model embeds into the genuine upper-half-plane
compactification as the all-interior-points-collapsed-at-I fiber. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Kontsevich.PlanarClusterInteriorEmbedding

open Configuration ForestDirectionRatioCoordinates ComplexConjugate Topology Set
open PlanarClusterDoubledData
open scoped Classical

variable {q : ℕ} (a b : Fin q)

/-- Existing collision machinery constructs actual positive configurations
I+epsilon*z from this datum, normalized at the original planar anchor. -/
def collisionData (z : PlanarClusterCompactification.Normalized a b) : InteriorCollisionData a 0 where
  base := fun _ => UpperHalfPlane.I
  velocity := z.val
  separated := fun _ _ _ h => z.property.1 h
  boundary := Fin.elim0
  boundary_strictMono := by intro i; exact Fin.elim0 i
  base_normalized := rfl
  velocity_normalized := z.property.2.1

private theorem upCross_ne : Complex.I - -Complex.I ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  norm_num at hi

private theorem downCross_ne : -Complex.I - Complex.I ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  norm_num at hi

private theorem phase_upCross : complexPhase (Complex.I - -Complex.I) = complexPhase Complex.I := by
  have h : Complex.I - -Complex.I = ((2 : ℝ) : ℂ) * Complex.I := by norm_num; ring
  rw [h, complexPhase_pos_real_mul (by norm_num : (0 : ℝ) < 2)]

private theorem phase_downCross : complexPhase (-Complex.I - Complex.I) = complexPhase (-Complex.I) := by
  have h : -Complex.I - Complex.I = ((2 : ℝ) : ℂ) * -Complex.I := by norm_num; ring
  rw [h, complexPhase_pos_real_mul (by norm_num : (0 : ℝ) < 2)]

private theorem phase_doubleI : complexPhase (Complex.I + Complex.I) = complexPhase Complex.I := by
  simpa only [sub_neg_eq_add] using phase_upCross

theorem lift_encode_direction (z : PlanarClusterCompactification.Normalized a b) (p : DoubledPair q 0) :
    (liftDR (PlanarClusterCompactification.encode a b z)).1 p = ((collisionData a b z).resolvedCoordinates 0).2.1 p := by
  rcases p with ⟨⟨u, v⟩, hp⟩
  rcases u with (u | u) | u <;> rcases v with (v | v) | v
  all_goals try exact Fin.elim0 u
  all_goals try exact Fin.elim0 v
  all_goals simp [liftDR, PlanarClusterDoubledData.direction, withinPair,
    PlanarClusterCompactification.encode, MarkedDRIdentification.ofPositions,
    InteriorCollisionData.resolvedCoordinates, InteriorCollisionData.activeDifference,
    InteriorCollisionData.pairBase, InteriorCollisionData.pairVelocity,
    InteriorCollisionData.doubledBase, InteriorCollisionData.doubledVelocity,
    collisionData, downCross_ne, phase_doubleI, phase_downCross,
    ← map_sub, complexPhase_conj]

private theorem norm_upCross : ‖Complex.I - -Complex.I‖ = 2 := by
  have h : Complex.I - -Complex.I = ((2 : ℝ) : ℂ) * Complex.I := by norm_num; ring
  rw [h, norm_mul]
  norm_num

private theorem norm_downCross : ‖-Complex.I - Complex.I‖ = 2 := by
  rw [norm_sub_rev]
  exact norm_upCross

private theorem norm_doubleI : ‖Complex.I + Complex.I‖ = 2 := by
  simpa only [sub_neg_eq_add] using norm_upCross

theorem lift_encode_ratio (z : PlanarClusterCompactification.Normalized a b) (t : DoubledTriple q 0) :
    (liftDR (PlanarClusterCompactification.encode a b z)).2 t = ((collisionData a b z).resolvedCoordinates 0).2.2 t := by
  rcases t with ⟨⟨u, v, w⟩, huv, huw⟩
  rcases u with (u | u) | u <;> rcases v with (v | v) | v <;> rcases w with (w | w) | w
  all_goals try exact Fin.elim0 u
  all_goals try exact Fin.elim0 v
  all_goals try exact Fin.elim0 w
  all_goals apply Subtype.ext
  all_goals norm_num [liftDR, PlanarClusterDoubledData.ratio, withinTriple,
    PlanarClusterCompactification.encode, MarkedDRIdentification.ofPositions,
    InteriorCollisionData.resolvedCoordinates, InteriorCollisionData.activeDifference,
    InteriorCollisionData.pairBase, InteriorCollisionData.pairVelocity,
    InteriorCollisionData.doubledBase, InteriorCollisionData.doubledVelocity,
    collisionData, upCross_ne, downCross_ne, normalizedNormRatio, norm_upCross,
    norm_downCross, norm_doubleI, ← map_sub, Complex.norm_conj, zeroRatio, oneRatio, halfRatio]

/-- The explicit doubled lift is exactly the already proved genuine
zero-scale collision limit of I+epsilon*z configurations. -/
theorem lift_encode_coordinates (z : PlanarClusterCompactification.Normalized a b) :
    liftCoordinates (PlanarClusterCompactification.encode a b z) = (collisionData a b z).resolvedCoordinates 0 := by
  apply Prod.ext
  · funext v
    rcases v with v | v
    · simp [liftCoordinates, InteriorCollisionData.resolvedCoordinates, InteriorCollisionData.doubledBase,
        InteriorCollisionData.doubledVelocity, collisionData]
    · exact Fin.elim0 v
  · exact Prod.ext (funext (lift_encode_direction a b z)) (funext (lift_encode_ratio a b z))

theorem lift_encode_mem (z : PlanarClusterCompactification.Normalized a b) :
    liftCoordinates (PlanarClusterCompactification.encode a b z) ∈ compactificationSet a 0 := by
  rw [lift_encode_coordinates]
  exact (collisionData a b z).zero_mem_compactification

/-- Membership extends from actual planar arrays to their entire compact
closure because the explicit full-data lift is continuous. -/
theorem lift_mem (x : PlanarClusterCompactification.Space a b) : liftCoordinates x.val ∈ compactificationSet a 0 := by
  have hc : IsClosed {y : Data (Fin q) | liftCoordinates y ∈ compactificationSet a 0} :=
    isClosed_closure.preimage continuous_liftCoordinates
  have hs : range (PlanarClusterCompactification.encode a b) ⊆
      {y : Data (Fin q) | liftCoordinates y ∈ compactificationSet a 0} := by
    rintro y ⟨z, rfl⟩
    exact lift_encode_mem a b z
  exact (closure_minimal hs hc) x.property

def embedding (x : PlanarClusterCompactification.Space a b) : Compactification a 0 :=
  ⟨liftCoordinates x.val, lift_mem a b x⟩

theorem continuous_embedding : Continuous (embedding a b) :=
  (continuous_liftCoordinates.comp continuous_subtype_val).subtype_mk _

theorem projectUpper_embedding (x : PlanarClusterCompactification.Space a b) :
    projectUpper (projectDR (embedding a b x).val) = x.val := projectUpper_liftDR x.val

theorem embedding_injective : Function.Injective (embedding a b) := by
  intro x y h
  apply Subtype.ext
  have he := congrArg (fun z : Compactification a 0 => projectUpper (projectDR z.val)) h
  simpa only [projectUpper_embedding] using he

theorem isClosedEmbedding_embedding : IsClosedEmbedding (embedding a b) :=
  (continuous_embedding a b).isClosedEmbedding (embedding_injective a b)

theorem embedding_position (x : PlanarClusterCompactification.Space a b) (j : Fin q) :
    (embedding a b x).val.1 (Sum.inl j) = (Complex.I : OnePoint ℂ) := rfl

theorem embedding_not_original (hab : a ≠ b) (x : PlanarClusterCompactification.Space a b) :
    embedding a b x ∉ range (compactificationEmbedding a : Configuration.Normalized a 0 → Compactification a 0) := by
  rintro ⟨c, hc⟩
  have ha := congrArg (fun y : Compactification a 0 => y.val.1 (Sum.inl a)) hc
  have hb := congrArg (fun y : Compactification a 0 => y.val.1 (Sum.inl b)) hc
  have he : (c.val.interior a : ℂ) = (c.val.interior b : ℂ) := by
    apply OnePoint.coe_injective
    exact ha.trans hb.symm
  exact hab (c.val.interior_injective (UpperHalfPlane.ext he))

theorem embedding_original (z : PlanarClusterCompactification.Normalized a b) :
    embedding a b (PlanarClusterCompactification.embedding a b z) = (collisionData a b z).boundaryPoint :=
  Subtype.ext (lift_encode_coordinates a b z)

end EnvelopingIsomorphism.Deformation.Kontsevich.PlanarClusterInteriorEmbedding
