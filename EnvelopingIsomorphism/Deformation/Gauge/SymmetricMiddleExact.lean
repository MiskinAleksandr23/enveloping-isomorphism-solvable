import EnvelopingIsomorphism.Deformation.Polyvectors
import EnvelopingIsomorphism.Deformation.LowArity

/-! Elementary middle exactness at a commutative product. A unary Hochschild
boundary is symmetric, whereas the normalized bivector inclusion is alternating.
Their equality forces both to vanish, and the remaining unary cochain is an
actual algebra derivation. No HKR cohomology comparison is used in this proof. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Gauge.SymmetricMiddle

variable {K A : Type*} [Field K] [CharZero K] [CommRing A] [Algebra K A]

omit [CharZero K] in
theorem differentialOne_symmetric (X : Unary K A) (a b : A) :
    differentialOne (LinearMap.mul K A) X a b = differentialOne (LinearMap.mul K A) X b a := by
  change X a * b + a * X b - X (a * b) = X b * a + b * X a - X (b * a)
  rw [mul_comm b a, mul_comm (X b) a, mul_comm b (X a), add_comm (a * X b)]

omit [CharZero K] in
theorem differentialZero_eq_zero (a : A) : differentialZero (LinearMap.mul K A) a = 0 := by
  apply LinearMap.ext
  intro b
  change a * b - b * a = 0
  rw [mul_comm, sub_self]

/-- A symmetric Hochschild boundary cannot equal a nonzero alternating cochain. -/
theorem alternating_coboundary_zero (B : Binary K A)
    (hB : ∀ a b, B b a = -B a b) (X : Unary K A)
    (h : B = -differentialOne (LinearMap.mul K A) X) :
    B = 0 ∧ differentialOne (LinearMap.mul K A) X = 0 := by
  have hs (a b : A) : B a b = B b a := by
    have h₁ := congrArg (fun F : Binary K A ↦ F a b) h
    have h₂ := congrArg (fun F : Binary K A ↦ F b a) h
    change B a b = -differentialOne (LinearMap.mul K A) X a b at h₁
    change B b a = -differentialOne (LinearMap.mul K A) X b a at h₂
    rw [differentialOne_symmetric X a b] at h₁
    exact h₁.trans h₂.symm
  have hz : B = 0 := by
    apply LinearMap.ext
    intro a
    apply LinearMap.ext
    intro b
    have he : B a b = -B a b := (hs a b).trans (hB a b)
    have htwo : (2 : K) • B a b = 0 := by
      rw [two_smul]
      exact (congrArg (fun z : A ↦ z + B a b) he).trans (neg_add_cancel _)
    exact (smul_eq_zero.mp htwo).resolve_left two_ne_zero
  refine ⟨hz, ?_⟩
  rw [hz] at h
  apply LinearMap.ext
  intro a
  apply LinearMap.ext
  intro b
  have he := congrArg (fun B : Binary K A ↦ B a b) h
  exact neg_eq_zero.mp he.symm

/-- Closed unary cochains are derivations, directly from their Hochschild equation. -/
def derivationOfClosed (X : Unary K A) (hX : differentialOne (LinearMap.mul K A) X = 0) :
    Derivation K A A :=
  Derivation.mk' X (by
    intro a b
    have h := congrArg (fun F : Binary K A ↦ F a b) hX
    change X a * b + a * X b - X (a * b) = 0 at h
    change X (a * b) = a * X b + b * X a
    simpa only [mul_comm (X a) b, add_comm] using (sub_eq_zero.mp h).symm)

omit [CharZero K] in
@[simp] theorem derivationOfClosed_toLinearMap (X : Unary K A)
    (hX : differentialOne (LinearMap.mul K A) X = 0) :
    (derivationOfClosed X hX).toLinearMap = X := rfl

def unaryInclusion : Multiderivation K A 1 →ₗ[K] Unary K A where
  toFun F := cochainOneEquiv K A F.val.toMultilinearMap
  map_add' F G := (cochainOneEquiv K A).map_add F.val.toMultilinearMap G.val.toMultilinearMap
  map_smul' c F := (cochainOneEquiv K A).map_smul c F.val.toMultilinearMap

def binaryInclusion : Multiderivation K A 2 →ₗ[K] Binary K A where
  toFun F := (2 : K)⁻¹ • cochainTwoEquiv K A F.val.toMultilinearMap
  map_add' F G := by
    rw [show (F + G).val.toMultilinearMap = F.val.toMultilinearMap + G.val.toMultilinearMap from rfl,
      map_add, smul_add]
  map_smul' c F := by
    change (2 : K)⁻¹ • cochainTwoEquiv K A (c • F.val.toMultilinearMap) =
      c • ((2 : K)⁻¹ • cochainTwoEquiv K A F.val.toMultilinearMap)
    exact (congrArg (fun z : Binary K A ↦ (2 : K)⁻¹ • z)
      ((cochainTwoEquiv K A).map_smul c F.val.toMultilinearMap)).trans (smul_comm _ _ _)

omit [CharZero K] in
theorem unaryInclusion_ofDerivation (D : Derivation K A A) :
    unaryInclusion (Multiderivation.ofDerivation D) = D.toLinearMap := by
  apply LinearMap.ext
  intro a
  rfl

omit [CharZero K] in
theorem binaryInclusion_apply (F : Multiderivation K A 2) (a b : A) :
    binaryInclusion F a b = (2 : K)⁻¹ • F ![a, b] := by
  have h := cochainTwoEquiv_symm_apply K A (cochainTwoEquiv K A F.val.toMultilinearMap) ![a, b]
  rw [LinearEquiv.symm_apply_apply] at h
  exact congrArg (fun z : A ↦ (2 : K)⁻¹ • z) h.symm

omit [CharZero K] in
theorem binaryInclusion_skew (F : Multiderivation K A 2) (a b : A) :
    binaryInclusion F b a = -binaryInclusion F a b := by
  have h := F.val.map_swap ![a, b] (by decide : (0 : Fin 2) ≠ 1)
  have hv : (![a, b] : Fin 2 → A) ∘ Equiv.swap 0 1 = ![b, a] := by
    funext i
    fin_cases i <;> rfl
  rw [hv] at h
  rw [binaryInclusion_apply, binaryInclusion_apply, h, smul_neg]

theorem binaryInclusion_eq_zero (F : Multiderivation K A 2) (hF : binaryInclusion F = 0) : F = 0 := by
  apply Multiderivation.ext
  intro a
  have h := congrArg (fun B : Binary K A ↦ B (a 0) (a 1)) hF
  rw [binaryInclusion_apply] at h
  have he : ![a 0, a 1] = a := by
    funext i
    fin_cases i <;> rfl
  rw [he] at h
  exact (smul_eq_zero.mp h).resolve_left (inv_ne_zero two_ne_zero)

/-- The elementary lifting statement supplies a vector field and the zero boundary. -/
theorem obstruction_lift (δ : Multiderivation K A 2) (X : Unary K A)
    (h : binaryInclusion δ = -differentialOne (LinearMap.mul K A) X) :
    δ = 0 ∧ ∃ Y : Multiderivation K A 1, X = unaryInclusion Y := by
  obtain ⟨hδ, hX⟩ := alternating_coboundary_zero (binaryInclusion δ) (binaryInclusion_skew δ) X h
  refine ⟨binaryInclusion_eq_zero δ hδ, Multiderivation.ofDerivation (derivationOfClosed X hX), ?_⟩
  rw [unaryInclusion_ofDerivation, derivationOfClosed_toLinearMap]

omit [CharZero K] in
theorem unaryInclusion_eq_derivation (F : Multiderivation K A 1) :
    unaryInclusion F = (Multiderivation.oneEquiv F).toLinearMap := by
  have h := congrArg unaryInclusion (Multiderivation.ofDerivation_oneEquiv F)
  rw [unaryInclusion_ofDerivation] at h
  exact h.symm

omit [CharZero K] in
theorem unaryInclusion_eq_hkr (F : Multiderivation K A 1) :
    unaryInclusion F = cochainOneEquiv K A (Multiderivation.toCochain F) := by
  change _ = cochainOneEquiv K A ((Nat.factorial 1 : K)⁻¹ • F.val.toMultilinearMap)
  simp [Nat.factorial, unaryInclusion]

theorem binaryInclusion_eq_hkr (F : Multiderivation K A 2) :
    binaryInclusion F = cochainTwoEquiv K A (Multiderivation.toCochain F) := by
  change _ = cochainTwoEquiv K A ((Nat.factorial 2 : K)⁻¹ • F.val.toMultilinearMap)
  rw [map_smul]
  norm_num [Nat.factorial, binaryInclusion]

def coboundary : Unary K A →ₗ[K] Binary K A where
  toFun := differentialOne (LinearMap.mul K A)
  map_add' X Y := by
    apply LinearMap.ext
    intro a
    apply LinearMap.ext
    intro b
    simp only [differentialOne_apply, LinearMap.add_apply, map_add]
    abel
  map_smul' c X := by
    apply LinearMap.ext
    intro a
    apply LinearMap.ext
    intro b
    simp only [differentialOne_apply, LinearMap.smul_apply, map_smul, smul_add, smul_sub, RingHom.id_apply]

omit [CharZero K] in
theorem coboundary_derivation (D : Derivation K A A) : coboundary D.toLinearMap = 0 := by
  apply LinearMap.ext
  intro a
  apply LinearMap.ext
  intro b
  change D a * b + a * D b - D (a * b) = 0
  rw [D.leibniz]
  simp only [smul_eq_mul, mul_comm (D a) b, add_comm, sub_self]

/-- The constant left operator for the low mapping-cone sequence. -/
def left : (Multiderivation K A 1 × A) →ₗ[K] (Multiderivation K A 2 × Unary K A) where
  toFun z := (0, unaryInclusion z.1)
  map_add' _ _ := by ext <;> simp
  map_smul' _ _ := by ext <;> simp

/-- The constant right operator; source differentials vanish at the commutative base. -/
def right : (Multiderivation K A 2 × Unary K A) →ₗ[K]
    (Multiderivation K A 3 × Binary K A) where
  toFun z := (0, binaryInclusion z.1 + coboundary z.2)
  map_add' _ _ := by
    apply Prod.ext
    · simp
    · simp only [Prod.fst_add, Prod.snd_add, map_add]
      abel
  map_smul' _ _ := by ext <;> simp

omit [CharZero K] in
@[simp] theorem left_apply (Y : Multiderivation K A 1) (u : A) :
    left (Y, u) = (0, unaryInclusion Y) := rfl

omit [CharZero K] in
@[simp] theorem right_apply (δ : Multiderivation K A 2) (X : Unary K A) :
    right (δ, X) = (0, binaryInclusion δ + differentialOne (LinearMap.mul K A) X) := rfl

omit [CharZero K] in
theorem right_left (z : Multiderivation K A 1 × A) : right (left z) = 0 := by
  change (0, binaryInclusion 0 + coboundary (unaryInclusion z.1)) = 0
  rw [map_zero, zero_add, unaryInclusion_eq_derivation, coboundary_derivation]
  rfl

/-- The actual base sequence is middle-exact by symmetry alone. -/
theorem range_left_eq_ker_right : LinearMap.range (left (K := K) (A := A)) = LinearMap.ker right := by
  apply le_antisymm
  · rintro z ⟨w, rfl⟩
    exact right_left w
  · rintro ⟨δ, X⟩ hz
    have h : binaryInclusion δ = -differentialOne (LinearMap.mul K A) X := by
      apply LinearMap.ext
      intro a
      apply LinearMap.ext
      intro b
      have he := congrArg (fun z : Multiderivation K A 3 × Binary K A ↦ z.2 a b)
        (show right (δ, X) = 0 from hz)
      change binaryInclusion δ a b + coboundary X a b = 0 at he
      exact eq_neg_of_add_eq_zero_left he
    obtain ⟨hδ, Y, hY⟩ := obstruction_lift δ X h
    refine ⟨(Y, 0), ?_⟩
    apply Prod.ext
    · exact hδ.symm
    · exact hY.symm

end EnvelopingIsomorphism.Deformation.Gauge.SymmetricMiddle
