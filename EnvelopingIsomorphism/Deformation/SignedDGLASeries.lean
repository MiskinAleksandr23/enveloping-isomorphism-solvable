import EnvelopingIsomorphism.Deformation.SignedDGLATransport
import EnvelopingIsomorphism.FormalSeries.LaurentBilinear

/-!
Actual Laurent coefficient extension of a signed DGLA. Every cochain degree is
completed separately; no common lower bound across all degrees is imposed.
-/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.SignedDGLA

open EnvelopingIsomorphism.FormalSeries
open LaurentModule

universe u v
variable {k : Type u} [Field k] (D : SignedDGLA.{u, v} k)

abbrev LaurentObj (p : ℤ) := LaurentModule k (D.Obj p)

@[reducible] def laurentObjects (p : ℤ) : ModuleCat.{v} (LaurentSeries k) :=
  ModuleCat.of (LaurentSeries k) (D.LaurentObj p)

def laurentD (p : ℤ) : D.LaurentObj p →ₗ[LaurentSeries k] D.LaurentObj (p + 1) :=
  LaurentModule.map (D.d p)

def laurentBracket (p q : ℤ) :
    D.LaurentObj p →ₗ[LaurentSeries k] D.LaurentObj q →ₗ[LaurentSeries k] D.LaurentObj (p + q) :=
  extendBilinear (D.bracket p q)

theorem laurentCongr {p q : ℤ} (h : p = q) (x : D.LaurentObj p) :
    gradedModuleCongr (LaurentSeries k) D.laurentObjects h x =
      LaurentModule.map (gradedModuleCongr k D.complex.X h).toLinearMap x := by
  subst q
  apply LaurentModule.ext
  intro d
  rfl

@[simp] theorem coeff_laurentD (p : ℤ) (x : D.LaurentObj p) (d : ℤ) :
    coeff (D.laurentD p x) d = D.d p (coeff x d) := rfl

theorem coeff_laurentBracket (p q : ℤ) (x : D.LaurentObj p) (y : D.LaurentObj q) (d : ℤ) :
    coeff (D.laurentBracket p q x y) d =
      ∑ᶠ a : Fin 2 → ℤ, if ∑ i, a i = d then D.bracket p q (coeff x (a 0)) (coeff y (a 1)) else 0 := rfl

theorem boundedBelow_laurentD (p : ℤ) (x : D.LaurentObj p) {b : ℤ} (hx : BoundedBelow b x) :
    BoundedBelow b (D.laurentD p x) := boundedBelow_map (D.d p) hx

theorem boundedBelow_laurentBracket (p q : ℤ) (x : D.LaurentObj p) (y : D.LaurentObj q)
    {b c : ℤ} (hx : BoundedBelow b x) (hy : BoundedBelow c y) :
    BoundedBelow (b + c) (D.laurentBracket p q x y) := boundedBelow_extendBilinear (D.bracket p q) x y hx hy

@[simp] theorem laurentD_single (p : ℤ) (e : ℤ) (x : D.Obj p) :
    D.laurentD p (single e x) = single e (D.d p x) := LaurentModule.map_single (D.d p) e x

theorem laurentBracket_single (p q : ℤ) (e d : ℤ) (x : D.Obj p) (y : D.Obj q) :
    D.laurentBracket p q (single e x) (single d y) = single (e + d) (D.bracket p q x y) :=
  extendBilinear_single (D.bracket p q) e d x y

theorem laurentD_sq (p : ℤ) (x : D.LaurentObj p) :
    D.laurentD (p + 1) (D.laurentD p x) = 0 := by
  apply LaurentModule.ext
  intro d
  simp only [coeff_laurentD, coeff_zero, D.d_sq]

def laurentComplex : CochainComplex (ModuleCat.{v} (LaurentSeries k)) ℤ :=
  CochainComplex.of D.laurentObjects (fun p ↦ ModuleCat.ofHom (D.laurentD p)) (by
    intro p
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact D.laurentD_sq p x)

@[simp] theorem laurentComplex_d (p : ℤ) :
    (D.laurentComplex.d p (p + 1)).hom = D.laurentD p := by
  simp only [laurentComplex, CochainComplex.of_d]
  rfl

private theorem bracket_skew_cast (p q : ℤ) (x : D.Obj p) (y : D.Obj q) :
    D.bracket p q x y = -((p * q).negOnePow : k) •
      gradedModuleCongr k D.complex.X (add_comm q p) (D.bracket q p y x) := by
  have hcast : HEq
      (-((p * q).negOnePow : k) • gradedModuleCongr k D.complex.X (add_comm q p) (D.bracket q p y x))
      (-((p * q).negOnePow : k) • D.bracket q p y x) := by
    rw [← map_smul]
    exact gradedModuleCongr_heq D.complex.X (add_comm q p) _
  exact eq_of_heq ((D.skew p q x y).trans hcast.symm)

theorem laurentBracket_skew_cast (p q : ℤ) (x : D.LaurentObj p) (y : D.LaurentObj q) :
    D.laurentBracket p q x y = -((p * q).negOnePow : k) •
      LaurentModule.map (gradedModuleCongr k D.complex.X (add_comm q p)).toLinearMap
        (D.laurentBracket q p y x) := by
  let F := restrictBilinear (D.laurentBracket p q)
  let C := (LaurentModule.map (gradedModuleCongr k D.complex.X (add_comm q p)).toLinearMap).restrictScalars k
  let G := -((p * q).negOnePow : k) • ((restrictBilinear (D.laurentBracket q p)).flip.compr₂ C)
  have heq : F = G := by
    apply bilinear_ext_of_bounded _ _ 0
    · intro x y b c hx hy
      change BoundedBelow ((b + c) + 0) (D.laurentBracket p q x y)
      simpa only [add_zero] using D.boundedBelow_laurentBracket p q x y hx hy
    · intro x y b c hx hy
      change BoundedBelow ((b + c) + 0) (-((p * q).negOnePow : k) •
        LaurentModule.map (gradedModuleCongr k D.complex.X (add_comm q p)).toLinearMap
          (D.laurentBracket q p y x))
      apply boundedBelow_smul
      apply boundedBelow_map
      simpa only [add_zero, add_comm c b] using D.boundedBelow_laurentBracket q p y x hy hx
    · intro e d v w
      change D.laurentBracket p q (single e v) (single d w) =
        -((p * q).negOnePow : k) •
          LaurentModule.map (gradedModuleCongr k D.complex.X (add_comm q p)).toLinearMap
            (D.laurentBracket q p (single d w) (single e v))
      rw [laurentBracket_single, laurentBracket_single, LaurentModule.map_single, add_comm d e,
        ← single_smul]
      exact congrArg (single (e + d)) (D.bracket_skew_cast p q v w)
  exact DFunLike.congr_fun (DFunLike.congr_fun heq x) y

theorem laurentBracket_skew (p q : ℤ) (x : D.LaurentObj p) (y : D.LaurentObj q) :
    HEq (D.laurentBracket p q x y)
      (-((p * q).negOnePow : LaurentSeries k) • D.laurentBracket q p y x) := by
  have hc (z : D.LaurentObj (p + q)) :
      -((p * q).negOnePow : LaurentSeries k) • z = -((p * q).negOnePow : k) • z := by
    simpa only [Int.cast_neg] using intCast_series_smul (k := k) (-((p * q).negOnePow : ℤ)) z
  have heq := D.laurentBracket_skew_cast p q x y
  rw [← hc, ← D.laurentCongr] at heq
  refine (heq_of_eq heq).trans ?_
  have ht := gradedModuleCongr_heq D.laurentObjects (add_comm q p)
    (-((p * q).negOnePow : LaurentSeries k) • D.laurentBracket q p y x)
  simpa only [map_smul] using ht

theorem laurentBracket_jacobi (p q r : ℤ)
    (x : D.LaurentObj p) (y : D.LaurentObj q) (z : D.LaurentObj r) :
    gradedModuleCongr (LaurentSeries k) D.laurentObjects (add_assoc p q r).symm
      (D.laurentBracket p (q + r) x (D.laurentBracket q r y z)) =
      D.laurentBracket (p + q) r (D.laurentBracket p q x y) z +
      ((p * q).negOnePow : LaurentSeries k) • gradedModuleCongr (LaurentSeries k) D.laurentObjects
        (by omega : q + (p + r) = (p + q) + r)
        (D.laurentBracket q (p + r) y (D.laurentBracket p r x z)) := by
  simp only [D.laurentCongr, intCast_series_smul]
  let B := fun p q ↦ restrictBilinear (D.laurentBracket p q)
  let CL := (LaurentModule.map (gradedModuleCongr k D.complex.X (add_assoc p q r).symm).toLinearMap).restrictScalars k
  let CR := (LaurentModule.map (gradedModuleCongr k D.complex.X
    (by omega : q + (p + r) = (p + q) + r)).toLinearMap).restrictScalars k
  let F := postTrilinear (nestRight (B p (q + r)) (B q r)) CL
  let G := (B p q).compr₂ (B (p + q) r) +
    ((p * q).negOnePow : k) • postTrilinear (nestRight (B q (p + r)) (B p r)).flip CR
  have heq : F = G := by
    apply trilinear_ext_of_bounded _ _ 0
    · intro x y z b c d hx hy hz
      change BoundedBelow (((b + c) + d) + 0)
        (LaurentModule.map (gradedModuleCongr k D.complex.X (add_assoc p q r).symm).toLinearMap
          (D.laurentBracket p (q + r) x (D.laurentBracket q r y z)))
      apply boundedBelow_map
      simpa only [add_zero, add_assoc] using D.boundedBelow_laurentBracket p (q + r)
        x (D.laurentBracket q r y z) hx (D.boundedBelow_laurentBracket q r y z hy hz)
    · intro x y z b c d hx hy hz
      change BoundedBelow (((b + c) + d) + 0)
        (D.laurentBracket (p + q) r (D.laurentBracket p q x y) z +
          ((p * q).negOnePow : k) • LaurentModule.map (gradedModuleCongr k D.complex.X
            (by omega : q + (p + r) = (p + q) + r)).toLinearMap
              (D.laurentBracket q (p + r) y (D.laurentBracket p r x z)))
      apply boundedBelow_add
      · simpa only [add_zero] using D.boundedBelow_laurentBracket (p + q) r
          (D.laurentBracket p q x y) z (D.boundedBelow_laurentBracket p q x y hx hy) hz
      · apply boundedBelow_smul
        apply boundedBelow_map
        have h := D.boundedBelow_laurentBracket q (p + r)
          y (D.laurentBracket p r x z) hy (D.boundedBelow_laurentBracket p r x z hx hz)
        convert h using 1
        omega
    · intro b c d f g h
      change LaurentModule.map (gradedModuleCongr k D.complex.X (add_assoc p q r).symm).toLinearMap
          (D.laurentBracket p (q + r) (single b f)
            (D.laurentBracket q r (single c g) (single d h))) =
        D.laurentBracket (p + q) r (D.laurentBracket p q (single b f) (single c g)) (single d h) +
          ((p * q).negOnePow : k) • LaurentModule.map (gradedModuleCongr k D.complex.X
            (by omega : q + (p + r) = (p + q) + r)).toLinearMap
              (D.laurentBracket q (p + r) (single c g)
                (D.laurentBracket p r (single b f) (single d h)))
      simp only [laurentBracket_single, LaurentModule.map_single]
      rw [show b + (c + d) = (b + c) + d by omega,
        show c + (b + d) = (b + c) + d by omega]
      have hj := congrArg (single (k := k) ((b + c) + d)) (D.jacobi p q r f g h)
      simp only [single_add, single_smul] at hj
      convert hj using 1 <;> rfl
  exact DFunLike.congr_fun (DFunLike.congr_fun (DFunLike.congr_fun heq x) y) z

theorem laurentD_bracket (p q : ℤ) (x : D.LaurentObj p) (y : D.LaurentObj q) :
    D.laurentD (p + q) (D.laurentBracket p q x y) =
      gradedModuleCongr (LaurentSeries k) D.laurentObjects (by omega : (p + 1) + q = (p + q) + 1)
        (D.laurentBracket (p + 1) q (D.laurentD p x) y) +
      (p.negOnePow : LaurentSeries k) • gradedModuleCongr (LaurentSeries k) D.laurentObjects
        (add_assoc p q 1).symm (D.laurentBracket p (q + 1) x (D.laurentD q y)) := by
  simp only [D.laurentCongr, intCast_series_smul]
  let B := fun p q ↦ restrictBilinear (D.laurentBracket p q)
  let CL := (LaurentModule.map (gradedModuleCongr k D.complex.X
    (by omega : (p + 1) + q = (p + q) + 1)).toLinearMap).restrictScalars k
  let CR := (LaurentModule.map (gradedModuleCongr k D.complex.X (add_assoc p q 1).symm).toLinearMap).restrictScalars k
  let F := (B p q).compr₂ ((D.laurentD (p + q)).restrictScalars k)
  let G := ((B (p + 1) q).comp ((D.laurentD p).restrictScalars k)).compr₂ CL +
    (p.negOnePow : k) • ((B p (q + 1)).compl₂ ((D.laurentD q).restrictScalars k)).compr₂ CR
  have heq : F = G := by
    apply bilinear_ext_of_bounded _ _ 0
    · intro x y b c hx hy
      change BoundedBelow ((b + c) + 0) (D.laurentD (p + q) (D.laurentBracket p q x y))
      apply D.boundedBelow_laurentD
      simpa only [add_zero] using D.boundedBelow_laurentBracket p q x y hx hy
    · intro x y b c hx hy
      change BoundedBelow ((b + c) + 0)
        (LaurentModule.map (gradedModuleCongr k D.complex.X
          (by omega : (p + 1) + q = (p + q) + 1)).toLinearMap
            (D.laurentBracket (p + 1) q (D.laurentD p x) y) +
        (p.negOnePow : k) • LaurentModule.map (gradedModuleCongr k D.complex.X (add_assoc p q 1).symm).toLinearMap
          (D.laurentBracket p (q + 1) x (D.laurentD q y)))
      apply boundedBelow_add
      · apply boundedBelow_map
        simpa only [add_zero] using D.boundedBelow_laurentBracket (p + 1) q
          (D.laurentD p x) y (D.boundedBelow_laurentD p x hx) hy
      · apply boundedBelow_smul
        apply boundedBelow_map
        simpa only [add_zero] using D.boundedBelow_laurentBracket p (q + 1)
          x (D.laurentD q y) hx (D.boundedBelow_laurentD q y hy)
    · intro b c f g
      change D.laurentD (p + q) (D.laurentBracket p q (single b f) (single c g)) =
        LaurentModule.map (gradedModuleCongr k D.complex.X
          (by omega : (p + 1) + q = (p + q) + 1)).toLinearMap
            (D.laurentBracket (p + 1) q (D.laurentD p (single b f)) (single c g)) +
        (p.negOnePow : k) • LaurentModule.map (gradedModuleCongr k D.complex.X (add_assoc p q 1).symm).toLinearMap
          (D.laurentBracket p (q + 1) (single b f) (D.laurentD q (single c g)))
      simp only [laurentD_single, laurentBracket_single, LaurentModule.map_single]
      have hd := congrArg (single (k := k) (b + c)) (D.d_bracket p q f g)
      simp only [single_add, single_smul] at hd
      convert hd using 1
      rfl
  exact DFunLike.congr_fun (DFunLike.congr_fun heq x) y

/-- The actual Laurent coefficient DGLA, completed independently in every degree. -/
def laurent : SignedDGLA.{u, v} (LaurentSeries k) where
  complex := D.laurentComplex
  bracket := D.laurentBracket
  skew := D.laurentBracket_skew
  jacobi := D.laurentBracket_jacobi
  differential_bracket p q f g := by
    simp only [laurentComplex_d]
    exact D.laurentD_bracket p q f g

@[simp] theorem laurent_d (p : ℤ) : D.laurent.d p = D.laurentD p := D.laurentComplex_d p

@[simp] theorem laurent_bracket (p q : ℤ) (x : D.LaurentObj p) (y : D.LaurentObj q) :
    D.laurent.bracket p q x y = D.laurentBracket p q x y := rfl

end EnvelopingIsomorphism.Deformation.SignedDGLA
