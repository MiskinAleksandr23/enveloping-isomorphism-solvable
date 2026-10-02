import EnvelopingIsomorphism.Deformation.Gauge.PathLift

/-! Bilinear polynomial-path calculus and transfer of algebraic composition
identities. Both formal parameters are handled by finite coefficient operations. -/

noncomputable section

namespace EnvelopingIsomorphism.Deformation.Gauge

open EnvelopingIsomorphism.FormalSeries PowerSeriesModule

variable {k A B C D P Q : Type*} [CommRing k]
  [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B]
  [AddCommGroup C] [Module k C] [AddCommGroup D] [Module k D]
  [AddCommGroup P] [Module k P] [AddCommGroup Q] [Module k Q]

def pathBilinear (f : A →ₗ[k] B →ₗ[k] C) :
    ModulePath k A →ₗ[PowerSeries k] ModulePath k B →ₗ[PowerSeries k] ModulePath k C :=
  PowerSeriesModule.extendBilinear (PolynomialModuleCalculus.extendBilinear f)

def pathMap (f : A →ₗ[k] B) : ModulePath k A →ₗ[PowerSeries k] ModulePath k B :=
  PowerSeriesModule.map (PolynomialModule.map k f)

theorem pathBilinear_derivative (f : A →ₗ[k] B →ₗ[k] C)
    (p : ModulePath k A) (q : ModulePath k B) :
    PolynomialModuleCalculus.seriesDerivative (pathBilinear f p q) =
      pathBilinear f (PolynomialModuleCalculus.seriesDerivative p) q + pathBilinear f p (PolynomialModuleCalculus.seriesDerivative q) := by
  apply PowerSeriesModule.ext
  intro n
  simp only [pathBilinear, PowerSeriesModule.extendBilinear_apply, coeffV_applyBilinear,
    PolynomialModuleCalculus.coeff_seriesDerivative, coeffV_add, map_sum, PolynomialModuleCalculus.derivative_extendBilinear,
    Finset.sum_add_distrib]

theorem pathBilinear_eval (f : A →ₗ[k] B →ₗ[k] C)
    (p : ModulePath k A) (q : ModulePath k B) (s : k) :
    PolynomialModuleCalculus.seriesEval s (pathBilinear f p q) =
      PowerSeriesModule.extendBilinear f (PolynomialModuleCalculus.seriesEval s p) (PolynomialModuleCalculus.seriesEval s q) := by
  apply PowerSeriesModule.ext
  intro n
  simp only [pathBilinear, PowerSeriesModule.extendBilinear_apply, coeffV_applyBilinear,
    PolynomialModuleCalculus.coeff_seriesEval, map_sum, PolynomialModuleCalculus.eval_extendBilinear]

private theorem polynomialBilinear_flip (f : A →ₗ[k] B →ₗ[k] C)
    (p : PolynomialModule k A) (q : PolynomialModule k B) :
    PolynomialModuleCalculus.extendBilinear f p q = PolynomialModuleCalculus.extendBilinear f.flip q p := by
  induction p using PolynomialModule.induction_linear with
  | zero => simp
  | add p p' hp hp' => simp [hp, hp']
  | single n a =>
    induction q using PolynomialModule.induction_linear with
    | zero => simp
    | add q q' hq hq' => simp [hq, hq']
    | single m b => simp [Nat.add_comm]

theorem pathBilinear_flip (f : A →ₗ[k] B →ₗ[k] C)
    (p : ModulePath k A) (q : ModulePath k B) :
    pathBilinear f p q = pathBilinear f.flip q p := by
  have hf : (PolynomialModuleCalculus.extendBilinear f).flip = PolynomialModuleCalculus.extendBilinear f.flip := by
    apply LinearMap.ext
    intro q
    apply LinearMap.ext
    intro p
    exact polynomialBilinear_flip f p q
  change applyBilinear (PolynomialModuleCalculus.extendBilinear f) p q = applyBilinear (PolynomialModuleCalculus.extendBilinear f.flip) q p
  rw [applyBilinear_flip, hf]

private theorem polynomialBilinear_assoc
    (f : A →ₗ[k] B →ₗ[k] P) (g : P →ₗ[k] C →ₗ[k] D)
    (f' : B →ₗ[k] C →ₗ[k] Q) (g' : A →ₗ[k] Q →ₗ[k] D)
    (h : ∀ a b c, g (f a b) c = g' a (f' b c))
    (p : PolynomialModule k A) (q : PolynomialModule k B) (r : PolynomialModule k C) :
    PolynomialModuleCalculus.extendBilinear g (PolynomialModuleCalculus.extendBilinear f p q) r =
      PolynomialModuleCalculus.extendBilinear g' p (PolynomialModuleCalculus.extendBilinear f' q r) := by
  induction p using PolynomialModule.induction_linear with
  | zero => simp
  | add p p' hp hp' => simp [hp, hp']
  | single i a =>
    induction q using PolynomialModule.induction_linear with
    | zero => simp
    | add q q' hq hq' => simp [hq, hq']
    | single j b =>
      induction r using PolynomialModule.induction_linear with
      | zero => simp
      | add r r' hr hr' => simp only [map_add, hr, hr']
      | single l c => simp [h, Nat.add_assoc]

/-- Any bilinear associativity identity lifts to complete polynomial paths. -/
theorem pathBilinear_assoc
    (f : A →ₗ[k] B →ₗ[k] P) (g : P →ₗ[k] C →ₗ[k] D)
    (f' : B →ₗ[k] C →ₗ[k] Q) (g' : A →ₗ[k] Q →ₗ[k] D)
    (h : ∀ a b c, g (f a b) c = g' a (f' b c))
    (p : ModulePath k A) (q : ModulePath k B) (r : ModulePath k C) :
    pathBilinear g (pathBilinear f p q) r = pathBilinear g' p (pathBilinear f' q r) := by
  apply PowerSeriesModule.ext
  intro n
  simp only [pathBilinear, PowerSeriesModule.extendBilinear_apply, coeffV_applyBilinear,
    map_sum, LinearMap.sum_apply]
  rw [sum_antidiagonal_assoc
    (fun i j l ↦ PolynomialModuleCalculus.extendBilinear g
      (PolynomialModuleCalculus.extendBilinear f (coeffV i p) (coeffV j q)) (coeffV l r)) n]
  apply Finset.sum_congr rfl
  intro ij hij
  apply Finset.sum_congr rfl
  intro jl hjl
  exact polynomialBilinear_assoc f g f' g' h _ _ _

theorem pathBilinear_commute (f : A →ₗ[k] C →ₗ[k] C) (g : B →ₗ[k] C →ₗ[k] C)
    (h : ∀ a b c, f a (g b c) = g b (f a c))
    (p : ModulePath k A) (q : ModulePath k B) (r : ModulePath k C) :
    pathBilinear f p (pathBilinear g q r) = pathBilinear g q (pathBilinear f p r) := by
  rw [pathBilinear_flip f p]
  rw [pathBilinear_assoc g f.flip f.flip g (fun b c a ↦ h a b c)]
  rw [← pathBilinear_flip f p r]

private theorem polynomialBilinear_map_left (T : A →ₗ[k] B) (f : B →ₗ[k] C →ₗ[k] D)
    (p : PolynomialModule k A) (q : PolynomialModule k C) :
    PolynomialModuleCalculus.extendBilinear f (PolynomialModule.map k T p) q = PolynomialModuleCalculus.extendBilinear (f.comp T) p q := by
  induction p using PolynomialModule.induction_linear with
  | zero => simp
  | add p p' hp hp' => simp [hp, hp']
  | single n a =>
    induction q using PolynomialModule.induction_linear with
    | zero => simp
    | add q q' hq hq' => simp only [map_add, hq, hq']
    | single m c => simp

theorem pathBilinear_map_left (T : A →ₗ[k] B) (f : B →ₗ[k] C →ₗ[k] D)
    (p : ModulePath k A) (q : ModulePath k C) :
    pathBilinear f (pathMap T p) q = pathBilinear (f.comp T) p q := by
  apply PowerSeriesModule.ext
  intro n
  simp only [pathBilinear, PowerSeriesModule.extendBilinear_apply, coeffV_applyBilinear,
    pathMap, coeffV_map, polynomialBilinear_map_left]

theorem pathMap_sub_maps (f g : A →ₗ[k] B) (p : ModulePath k A) :
    pathMap (f - g) p = pathMap f p - pathMap g p := by
  apply PowerSeriesModule.ext
  intro n
  apply PolynomialModule.ext
  ext i
  simp [pathMap, PolynomialModule.map]
  rfl

/-- Coefficientwise operator-valued maps agree with the actual path operator. -/
theorem pathOperator_pathMap (T : A →ₗ[k] Module.End k B)
    (p : ModulePath k A) (q : ModulePath k B) :
    pathOperator (pathMap T p) q = pathBilinear T p q := by
  change pathBilinear (LinearMap.id : Module.End k B →ₗ[k] B →ₗ[k] B) (pathMap T p) q = _
  rw [pathBilinear_map_left, LinearMap.id_comp]

theorem pathOperator_sub (L M : ModulePath k (Module.End k B)) (b : ModulePath k B) :
    pathOperator (L - M) b = pathOperator L b - pathOperator M b := by
  change pathBilinear (LinearMap.id : Module.End k B →ₗ[k] B →ₗ[k] B) (L - M) b = _
  rw [map_sub, LinearMap.sub_apply]
  rfl

end EnvelopingIsomorphism.Deformation.Gauge
