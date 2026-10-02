import EnvelopingIsomorphism.Identification.LeadingDerivation
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Algebra.Algebra.Operations

/-! Leading operators on a filtered associative product become derivations
for its graded commutative product, in split basis coordinates. -/

noncomputable section
namespace EnvelopingIsomorphism.Identification

variable {R A ι : Type*} [CommRing R] [CommRing A] [Algebra R A]
  (b : Module.Basis ι R A) (ω : ι → ℕ)

theorem basisSupport_mul_le {s t u : Set ι}
    (hmul : ∀ i ∈ s, ∀ j ∈ t, b i * b j ∈ basisSupport b u) :
    basisSupport b s * basisSupport b t ≤ basisSupport b u := by
  rw [basisSupport, basisSupport, Submodule.span_mul_span]
  apply Submodule.span_le.mpr
  rintro _ ⟨_, ⟨i, hi, rfl⟩, _, ⟨j, hj, rfl⟩, rfl⟩
  exact hmul i hi j hj

theorem bilinear_mem_basisSupport (B : A →ₗ[R] A →ₗ[R] A) {s t u : Set ι}
    (hB : ∀ i ∈ s, ∀ j ∈ t, B (b i) (b j) ∈ basisSupport b u)
    {x y : A} (hx : x ∈ basisSupport b s) (hy : y ∈ basisSupport b t) :
    B x y ∈ basisSupport b u := by
  apply mapsTo_basisSupport b (B.flip y) _ x hx
  intro i hi
  exact mapsTo_basisSupport b (B (b i)) (hB i hi) y hy

variable
  (hmul : ∀ i j, b i * b j ∈ basisHomogeneous b ω (ω i + ω j))

include hmul

theorem homogeneous_mul_mem {d e : ℕ} {x y : A}
    (hx : x ∈ basisHomogeneous b ω d) (hy : y ∈ basisHomogeneous b ω e) :
    x * y ∈ basisHomogeneous b ω (d + e) := by
  apply (basisSupport_mul_le b _ (Submodule.mul_mem_mul hx hy))
  intro i hi j hj
  change ω i = d at hi
  change ω j = e at hj
  simpa only [basisHomogeneous, hi, hj] using hmul i j

theorem strict_mul_upper_mem {d e : ℕ} {x y : A}
    (hx : x ∈ basisStrict b ω d) (hy : y ∈ basisUpper b ω e) :
    x * y ∈ basisStrict b ω (d + e) := by
  apply (basisSupport_mul_le b _ (Submodule.mul_mem_mul hx hy))
  intro i hi j hj
  apply basisSupport_mono b _ (hmul i j)
  intro l hl
  change ω i < d at hi
  change ω j ≤ e at hj
  change ω l = ω i + ω j at hl
  change ω l < d + e
  omega

theorem upper_mul_upper_mem {d e : ℕ} {x y : A}
    (hx : x ∈ basisUpper b ω d) (hy : y ∈ basisUpper b ω e) :
    x * y ∈ basisUpper b ω (d + e) := by
  apply (basisSupport_mul_le b _ (Submodule.mul_mem_mul hx hy))
  intro i hi j hj
  apply basisSupport_mono b _ (hmul i j)
  intro l hl
  change ω i ≤ d at hi
  change ω j ≤ e at hj
  change ω l = ω i + ω j at hl
  change ω l ≤ d + e
  omega

omit hmul in
theorem homogeneous_mem_upper {d : ℕ} {x : A}
    (hx : x ∈ basisHomogeneous b ω d) : x ∈ basisUpper b ω d :=
  basisSupport_mono b (fun _ h => h.le) hx

/-- The leading operator of a derivation for a filtered product obeys the
Leibniz rule for the graded product. The product approximation is a genuine
filtration estimate; no derivation property of the leading operator is assumed. -/
theorem leadingOperator_leibniz_of_filtered_product
    (star : A →ₗ[R] A →ₗ[R] A)
    (hstar : ∀ d e x, x ∈ basisUpper b ω d →
      ∀ y, y ∈ basisUpper b ω e → star x y - x * y ∈ basisStrict b ω (d + e))
    (D : Module.End R A) (r : ℕ)
    (hD : ∀ i, D (b i) ∈ basisUpper b ω (ω i + r))
    (hLeibniz : ∀ x y, D (star x y) = star (D x) y + star x (D y)) :
    ∀ x y, leadingOperator b ω D r (x * y) =
      leadingOperator b ω D r x * y + x * leadingOperator b ω D r y := by
  let E := leadingOperator b ω D r
  have hE := leadingOperator_basis_homogeneous b ω D r
  have hDE := leadingOperator_basis_remainder b ω D r hD
  have hb (i j : ι) : E (b i * b j) = E (b i) * b j + b i * E (b j) := by
    let d := ω i
    let e := ω j
    let S := basisStrict b ω (d + e + r)
    have hi : b i ∈ basisHomogeneous b ω d := basis_mem_basisSupport b rfl
    have hj : b j ∈ basisHomogeneous b ω e := basis_mem_basisSupport b rfl
    have hiu := homogeneous_mem_upper b ω hi
    have hju := homogeneous_mem_upper b ω hj
    have hprod := homogeneous_mul_mem b ω hmul hi hj
    have h₁ : D (star (b i) (b j) - b i * b j) ∈ S :=
      shifts_strict_of_shifts_basis b ω D r hD (d + e) _
        (hstar d e _ hiu _ hju)
    have h₂ : star (D (b i)) (b j) - D (b i) * b j ∈ S := by
      simpa only [S, Nat.add_right_comm] using hstar (d + r) e _ (hD i) _ hju
    have h₃ : star (b i) (D (b j)) - b i * D (b j) ∈ S := by
      simpa only [S, Nat.add_assoc] using hstar d (e + r) _ hiu _ (hD j)
    have h₄ : (D (b i) - E (b i)) * b j ∈ S := by
      simpa only [S, Nat.add_right_comm] using strict_mul_upper_mem b ω hmul (hDE i) hju
    have h₅ : b i * (D (b j) - E (b j)) ∈ S := by
      have h := strict_mul_upper_mem b ω hmul (hDE j) hiu
      simpa only [S, E, d, e, mul_comm, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h
    have h₆ : D (b i * b j) - E (b i * b j) ∈ S :=
      remainder_strict_of_basis b ω D E r hDE (d + e) _ hprod
    have hlow : E (b i * b j) - (E (b i) * b j + b i * E (b j)) ∈ S := by
      have h := S.sub_mem (S.add_mem (S.add_mem (S.add_mem
        (S.add_mem (S.neg_mem h₁) h₂) h₃) h₄) h₅) h₆
      convert h using 1
      simp only [map_sub, hLeibniz, sub_mul, mul_sub]
      abel
    have heprod := shifts_homogeneous_of_shifts_basis b ω E r hE (d + e) _ hprod
    have heleft : E (b i) * b j ∈ basisHomogeneous b ω (d + e + r) := by
      simpa only [Nat.add_right_comm] using homogeneous_mul_mem b ω hmul (hE i) hj
    have heright : b i * E (b j) ∈ basisHomogeneous b ω (d + e + r) := by
      simpa only [Nat.add_assoc] using homogeneous_mul_mem b ω hmul hi (hE j)
    have hhom := (basisHomogeneous b ω (d + e + r)).sub_mem heprod
      ((basisHomogeneous b ω (d + e + r)).add_mem heleft heright)
    exact sub_eq_zero.mp (eq_zero_of_homogeneous_and_strict b ω hhom hlow)
  intro x y
  have hx : x ∈ Submodule.span R (Set.range b) := by rw [b.span_eq]; trivial
  have hy : y ∈ Submodule.span R (Set.range b) := by rw [b.span_eq]; trivial
  change E (x * y) = E x * y + x * E y
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy => obtain ⟨j, rfl⟩ := hy; exact hb i j
    | zero => simp
    | add y z _ _ hy hz => simp only [mul_add, map_add, hy, hz]; abel
    | smul a y _ hy => simp only [Algebra.mul_smul_comm, map_smul, hy, smul_add]
  | zero => simp
  | add x z _ _ hx hz => simp only [add_mul, map_add, hx, hz]; abel
  | smul a x _ hx => simp only [smul_mul_assoc, map_smul, hx, smul_add]

/-- Bundle the canonically extracted operator as a standard derivation. -/
def leadingDerivationOfFilteredProduct
    (star : A →ₗ[R] A →ₗ[R] A)
    (hstar : ∀ d e x, x ∈ basisUpper b ω d →
      ∀ y, y ∈ basisUpper b ω e → star x y - x * y ∈ basisStrict b ω (d + e))
    (D : Module.End R A) (r : ℕ)
    (hD : ∀ i, D (b i) ∈ basisUpper b ω (ω i + r))
    (hLeibniz : ∀ x y, D (star x y) = star (D x) y + star x (D y)) :
    Derivation R A A :=
  Derivation.mk' (leadingOperator b ω D r) (fun x y => by
    simpa only [smul_eq_mul, mul_comm, add_comm] using
      leadingOperator_leibniz_of_filtered_product b ω hmul star hstar D r hD hLeibniz x y)

end EnvelopingIsomorphism.Identification
