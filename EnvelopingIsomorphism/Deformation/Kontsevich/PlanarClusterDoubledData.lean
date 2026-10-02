import EnvelopingIsomorphism.Deformation.Kontsevich.PlanarClusterCompactification
import EnvelopingIsomorphism.Deformation.Kontsevich.InteriorClusterChart

/-! Continuous full doubled data of a planar cluster collapsed at I. The
upper and lower copies retain the planar coordinates, while cross-copy
directions and ratios have their literal fixed collision values. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace EnvelopingIsomorphism.Deformation.Kontsevich.PlanarClusterDoubledData

open Configuration ForestDirectionRatioCoordinates ComplexConjugate Topology
open scoped Classical

variable {q : ℕ}

def signedLabel : DoubledLabel q 0 ≃ Bool × Fin q where
  toFun j := match j with
    | Sum.inl (Sum.inl i) => (false, i)
    | Sum.inl (Sum.inr i) => Fin.elim0 i
    | Sum.inr i => (true, i)
  invFun j := if j.1 then Sum.inr j.2 else Sum.inl (Sum.inl j.2)
  left_inv j := by
    rcases j with (j | j) | j
    · rfl
    · exact Fin.elim0 j
    · rfl
  right_inv j := by rcases j with ⟨b, j⟩; cases b <;> rfl

def lower (j : DoubledLabel q 0) : Bool := (signedLabel j).1
def index (j : DoubledLabel q 0) : Fin q := (signedLabel j).2

@[simp] theorem lower_upper (j : Fin q) : lower (Sum.inl (Sum.inl j)) = false := rfl
@[simp] theorem lower_lower (j : Fin q) : lower (Sum.inr j) = true := rfl
@[simp] theorem index_upper (j : Fin q) : index (Sum.inl (Sum.inl j)) = j := rfl
@[simp] theorem index_lower (j : Fin q) : index (Sum.inr j) = j := rfl

def withinPair (p : DoubledPair q 0) (hp : lower p.val.1 = lower p.val.2) : Pair (Fin q) :=
  ⟨(index p.val.1, index p.val.2), fun h => p.property (signedLabel.injective (Prod.ext hp h))⟩

def withinTriple (t : DoubledTriple q 0)
    (h₁ : lower t.val.1 = lower t.val.2.1) (h₂ : lower t.val.1 = lower t.val.2.2) : Triple (Fin q) :=
  ⟨(index t.val.1, index t.val.2.1, index t.val.2.2),
    (withinPair ⟨(t.val.1, t.val.2.1), t.property.1⟩ h₁).property,
    (withinPair ⟨(t.val.1, t.val.2.2), t.property.2⟩ h₂).property⟩

def direction (x : Data (Fin q)) (p : DoubledPair q 0) : Circle :=
  if hp : lower p.val.1 = lower p.val.2 then
    if lower p.val.1 then (x.1 (withinPair p hp))⁻¹ else x.1 (withinPair p hp)
  else if lower p.val.1 then complexPhase Complex.I else complexPhase (-Complex.I)

def zeroRatio : Set.Icc (0 : ℝ) 1 := ⟨0, by constructor <;> norm_num⟩
def oneRatio : Set.Icc (0 : ℝ) 1 := ⟨1, by constructor <;> norm_num⟩
def halfRatio : Set.Icc (0 : ℝ) 1 := ⟨1 / 2, by constructor <;> norm_num⟩

def ratio (x : Data (Fin q)) (t : DoubledTriple q 0) : Set.Icc (0 : ℝ) 1 :=
  if h₁ : lower t.val.1 = lower t.val.2.1 then
    if h₂ : lower t.val.1 = lower t.val.2.2 then x.2 (withinTriple t h₁ h₂) else zeroRatio
  else if lower t.val.1 = lower t.val.2.2 then oneRatio else halfRatio

/-- All pair directions and all normalized triple ratios are retained. -/
def liftDR (x : Data (Fin q)) : DRData q 0 := (direction x, ratio x)

theorem continuous_liftDR : Continuous (liftDR (q := q)) := by
  apply Continuous.prodMk
  · apply continuous_pi
    intro p
    unfold direction
    split_ifs <;> fun_prop
  · apply continuous_pi
    intro t
    unfold ratio
    split_ifs <;> fun_prop

def upperPair (p : Pair (Fin q)) : DoubledPair q 0 :=
  ⟨(Sum.inl (Sum.inl p.val.1), Sum.inl (Sum.inl p.val.2)), fun h => p.property (Sum.inl.inj (Sum.inl.inj h))⟩

def upperTriple (t : Triple (Fin q)) : DoubledTriple q 0 :=
  ⟨(Sum.inl (Sum.inl t.val.1), Sum.inl (Sum.inl t.val.2.1), Sum.inl (Sum.inl t.val.2.2)),
    fun h => t.property.1 (Sum.inl.inj (Sum.inl.inj h)),
    fun h => t.property.2 (Sum.inl.inj (Sum.inl.inj h))⟩

def projectUpper (x : DRData q 0) : Data (Fin q) :=
  (fun p => x.1 (upperPair p), fun t => x.2 (upperTriple t))

theorem continuous_projectUpper : Continuous (projectUpper (q := q)) := by
  unfold projectUpper
  fun_prop

theorem projectUpper_liftDR (x : Data (Fin q)) : projectUpper (liftDR x) = x := by
  apply Prod.ext
  · funext p
    simp [projectUpper, liftDR, direction, upperPair, withinPair]
  · funext t
    simp [projectUpper, liftDR, ratio, upperTriple, withinTriple]

theorem liftDR_injective : Function.Injective (liftDR (q := q)) :=
  Function.LeftInverse.injective projectUpper_liftDR

/-- Original stored positions are all I; reflected lower positions are encoded
by the corresponding lower and cross-copy DR entries. -/
def liftCoordinates (x : Data (Fin q)) : CompactCoordinateSpace q 0 :=
  (fun _ => (Complex.I : OnePoint ℂ), liftDR x)

theorem continuous_liftCoordinates : Continuous (liftCoordinates (q := q)) :=
  continuous_const.prodMk continuous_liftDR

theorem liftCoordinates_injective : Function.Injective (liftCoordinates (q := q)) :=
  fun _ _ h => liftDR_injective (congrArg Prod.snd h)

end EnvelopingIsomorphism.Deformation.Kontsevich.PlanarClusterDoubledData
