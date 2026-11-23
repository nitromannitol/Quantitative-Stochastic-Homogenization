import QuantitativeStochasticHomogenization.AppD.HeatSmoothing
import QuantitativeStochasticHomogenization.Ch03.Sec03.SkewHessian
import QuantitativeStochasticHomogenization.Ch03.Sec03.HarmonicExpansionBall
import QuantitativeStochasticHomogenization.Ch03.Sec03.EllipsoidSmoothTransfer
import QuantitativeStochasticHomogenization.Ch03.Sec03.TestMollification
import QuantitativeStochasticHomogenization.Ch06.Sec01.HeatFormulaLocal

/-!
# Iterated coordinate derivatives of compact tests

Calculus for the compact tests of the finite-ball estimate (consultant note T22, (2)) of the
proof of Lemma 4.21 in Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and
Large-Scale Regularity*.

For `α : Fin j → Fin d` the iterated coordinate derivative `iterDeriv α f` differentiates first in
the direction `α 0`. For smooth `f` it commutes with every coordinate derivative, it is linear,
the dilation `f(b⁻¹ ·)` has `iterDeriv α (f(b⁻¹ ·)) = b^{-j} (iterDeriv α f)(b⁻¹ ·)`, and for a
matrix `A` with entries in `[-1, 1]` the derivatives of order `j` of `f ∘ A` are at most `d^j`
times a bound of those of `f`.

The iterated mean value inequality (`abs_le_of_iterDeriv_le`) bounds `|f(x)|` on `B_t` by
`∑_{j < n} t^j ∑_α |∂^α f(0)| + t^n ∑_β A_β`, where `A_β` bounds `|∂^β f|` on `B_t` for the
derivatives of order `n`: the mean value inequality along `[0, x]` applied `n` times.
-/

open MeasureTheory
open scoped ContDiff

noncomputable section

namespace QSH

variable {d : ℕ}

/-! ## Iterated coordinate derivatives -/

/-- The iterated coordinate derivative `∂^α f`, differentiating first in the direction `α 0`. -/
def iterDeriv : {j : ℕ} → (Fin j → Fin d) → (Vec d → ℝ) → Vec d → ℝ
  | 0, _, f => f
  | _ + 1, α, f => iterDeriv (Fin.tail α) (coordinateDerivative (α 0) f)

@[simp] theorem iterDeriv_zero (α : Fin 0 → Fin d) (f : Vec d → ℝ) : iterDeriv α f = f := rfl

theorem iterDeriv_succ {j : ℕ} (α : Fin (j + 1) → Fin d) (f : Vec d → ℝ) :
    iterDeriv α f = iterDeriv (Fin.tail α) (coordinateDerivative (α 0) f) := rfl

theorem iterDeriv_cons {j : ℕ} (i : Fin d) (α : Fin j → Fin d) (f : Vec d → ℝ) :
    iterDeriv (Fin.cons i α : Fin (j + 1) → Fin d) f = iterDeriv α (coordinateDerivative i f) := by
  rw [iterDeriv_succ, Fin.tail_cons, Fin.cons_zero]

theorem contDiff_iterDeriv {j : ℕ} (α : Fin j → Fin d) {f : Vec d → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (iterDeriv α f) := by
  induction j generalizing f with
  | zero => exact hf
  | succ j ih => exact ih _ (contDiff_coordinateDerivative hf _)

theorem hasCompactSupport_iterDeriv {j : ℕ} (α : Fin j → Fin d) {f : Vec d → ℝ}
    (hf : HasCompactSupport f) : HasCompactSupport (iterDeriv α f) := by
  induction j generalizing f with
  | zero => exact hf
  | succ j ih => exact ih _ (hasCompactSupport_coordinateDerivative hf _)

theorem tsupport_coordinateDerivative_subset (i : Fin d) (f : Vec d → ℝ) :
    tsupport (coordinateDerivative i f) ⊆ tsupport f :=
  tsupport_fderiv_apply_subset ℝ (unitVector i)

theorem tsupport_iterDeriv_subset {j : ℕ} (α : Fin j → Fin d) (f : Vec d → ℝ) :
    tsupport (iterDeriv α f) ⊆ tsupport f := by
  induction j generalizing f with
  | zero => exact le_rfl
  | succ j ih => exact (ih _ _).trans (tsupport_coordinateDerivative_subset _ _)

theorem iterDeriv_eq_zero_of_notMem_tsupport {j : ℕ} (α : Fin j → Fin d) {f : Vec d → ℝ}
    {x : Vec d} (hx : x ∉ tsupport f) : iterDeriv α f x = 0 :=
  image_eq_zero_of_notMem_tsupport fun h => hx (tsupport_iterDeriv_subset α f h)

/-- **Coordinate derivatives commute with iterated derivatives** of smooth functions. -/
theorem coordinateDerivative_iterDeriv {j : ℕ} (α : Fin j → Fin d) {f : Vec d → ℝ}
    (hf : ContDiff ℝ ∞ f) (m : Fin d) :
    coordinateDerivative m (iterDeriv α f) = iterDeriv α (coordinateDerivative m f) := by
  induction j generalizing f with
  | zero => rfl
  | succ j ih =>
    rw [iterDeriv_succ, iterDeriv_succ, ih _ (contDiff_coordinateDerivative hf _)]
    congr 1
    funext x
    exact coordinateDerivative_comm_of_contDiff_two (hf.of_le (by simp)) m (α 0) x

/-! ## Linearity -/

theorem coordinateDerivative_const_mul' {f : Vec d → ℝ} (hf : Differentiable ℝ f) (c : ℝ)
    (i : Fin d) :
    coordinateDerivative i (fun x => c * f x) = fun x => c * coordinateDerivative i f x := by
  funext x
  have h := coordinateDerivative_sum_const_mul (Finset.univ : Finset Unit) (fun _ => c)
    (G := fun _ => f) (fun _ => hf) i x
  simpa using h

theorem iterDeriv_const_mul {j : ℕ} (α : Fin j → Fin d) {f : Vec d → ℝ} (hf : ContDiff ℝ ∞ f)
    (c : ℝ) : iterDeriv α (fun x => c * f x) = fun x => c * iterDeriv α f x := by
  induction j generalizing f with
  | zero => rfl
  | succ j ih =>
    rw [iterDeriv_succ, iterDeriv_succ,
      coordinateDerivative_const_mul' (hf.differentiable (by simp)) c,
      ih _ (contDiff_coordinateDerivative hf _)]

theorem iterDeriv_sum_const_mul {ι : Type*} (s : Finset ι) (c : ι → ℝ) {G : ι → Vec d → ℝ}
    (hG : ∀ l, ContDiff ℝ ∞ (G l)) {j : ℕ} (α : Fin j → Fin d) :
    iterDeriv α (fun x => ∑ l ∈ s, c l * G l x) = fun x => ∑ l ∈ s, c l * iterDeriv α (G l) x := by
  induction j generalizing G with
  | zero => rfl
  | succ j ih =>
    rw [iterDeriv_succ]
    have h : coordinateDerivative (α 0) (fun x => ∑ l ∈ s, c l * G l x) =
        fun x => ∑ l ∈ s, c l * coordinateDerivative (α 0) (G l) x := by
      funext x
      exact coordinateDerivative_sum_const_mul s c (fun l => (hG l).differentiable (by simp)) _ x
    rw [h, ih (fun l => contDiff_coordinateDerivative (hG l) _)]
    rfl

/-! ## Dilations, reflections and linear changes of variables -/

/-- The dilation `f(b⁻¹ ·)`. -/
def dilate (b : ℝ) (f : Vec d → ℝ) : Vec d → ℝ := fun z => f (b⁻¹ • z)

theorem contDiff_dilate {f : Vec d → ℝ} (hf : ContDiff ℝ ∞ f) (b : ℝ) :
    ContDiff ℝ ∞ (dilate b f) :=
  hf.comp (contDiff_const_smul _)

theorem coordinateDerivative_dilate {f : Vec d → ℝ} (hf : Differentiable ℝ f) (b : ℝ)
    (i : Fin d) :
    coordinateDerivative i (dilate b f) = fun z => b⁻¹ * dilate b (coordinateDerivative i f) z := by
  funext z
  have h : HasFDerivAt (dilate b f)
      ((fderiv ℝ f (b⁻¹ • z)).comp (b⁻¹ • ContinuousLinearMap.id ℝ (Vec d))) z := by
    have h1 : HasFDerivAt (fun z : Vec d => b⁻¹ • z) (b⁻¹ • ContinuousLinearMap.id ℝ (Vec d)) z :=
      (hasFDerivAt_id (𝕜 := ℝ) z).const_smul b⁻¹
    exact (hf _).hasFDerivAt.comp z h1
  unfold coordinateDerivative
  rw [h.fderiv]
  show fderiv ℝ f (b⁻¹ • z) (b⁻¹ • unitVector i) = b⁻¹ * fderiv ℝ f (b⁻¹ • z) (unitVector i)
  rw [map_smul, smul_eq_mul]

theorem iterDeriv_dilate {j : ℕ} (α : Fin j → Fin d) {f : Vec d → ℝ} (hf : ContDiff ℝ ∞ f)
    (b : ℝ) : iterDeriv α (dilate b f) = fun z => (b⁻¹) ^ j * dilate b (iterDeriv α f) z := by
  induction j generalizing f with
  | zero => funext z; simp
  | succ j ih =>
    rw [iterDeriv_succ, coordinateDerivative_dilate (hf.differentiable (by simp)),
      iterDeriv_const_mul _ (contDiff_dilate (contDiff_coordinateDerivative hf _) b),
      ih _ (contDiff_coordinateDerivative hf _)]
    funext z
    simp only [dilate, iterDeriv_succ]
    ring

theorem coordinateDerivative_comp_sub' {f : Vec d → ℝ} (hf : Differentiable ℝ f) (x : Vec d)
    (i : Fin d) :
    coordinateDerivative i (fun w => f (x - w)) = fun w => -coordinateDerivative i f (x - w) := by
  funext w
  have h : HasFDerivAt (fun w => f (x - w))
      ((fderiv ℝ f (x - w)).comp (-ContinuousLinearMap.id ℝ (Vec d))) w := by
    have h1 : HasFDerivAt (fun w : Vec d => x - w) (-ContinuousLinearMap.id ℝ (Vec d)) w := by
      simpa using (hasFDerivAt_id (𝕜 := ℝ) w).const_sub x
    exact (hf _).hasFDerivAt.comp w h1
  unfold coordinateDerivative
  rw [h.fderiv]
  simp

/-- The second derivatives of the reflection `w ↦ f(x - w)`. -/
theorem coordinateDerivative_coordinateDerivative_comp_sub {f : Vec d → ℝ}
    (hf : ContDiff ℝ ∞ f) (x : Vec d) (i j : Fin d) :
    coordinateDerivative j (coordinateDerivative i (fun w => f (x - w))) =
      fun w => coordinateDerivative j (coordinateDerivative i f) (x - w) := by
  have hdi : Differentiable ℝ (coordinateDerivative i f) :=
    (contDiff_coordinateDerivative hf i).differentiable (by simp)
  have hd2 : Differentiable ℝ (fun w => coordinateDerivative i f (x - w)) :=
    hdi.comp ((differentiable_const _).sub differentiable_id)
  have e1 : coordinateDerivative i (fun w => f (x - w)) =
      fun w => (-1) * coordinateDerivative i f (x - w) := by
    rw [coordinateDerivative_comp_sub' (hf.differentiable (by simp))]
    funext w
    ring
  rw [e1, coordinateDerivative_const_mul' (f := fun w => coordinateDerivative i f (x - w)) hd2,
    coordinateDerivative_comp_sub' hdi]
  funext w
  ring

/-- The chain rule for `f ∘ A` with an invertible matrix `A`. -/
theorem coordinateDerivative_comp_mulVec' {A : Mat d} (hA : A.det ≠ 0) (f : Vec d → ℝ)
    (i : Fin d) :
    coordinateDerivative i (fun y => f (A.mulVec y)) =
      fun y => ∑ l, A l i * coordinateDerivative l f (A.mulVec y) := by
  funext y
  exact coordinateDerivative_comp_mulVec hA f i y

theorem contDiff_comp_mulVec {f : Vec d → ℝ} (hf : ContDiff ℝ ∞ f) (A : Mat d) :
    ContDiff ℝ ∞ (fun y => f (A.mulVec y)) :=
  hf.comp (Matrix.mulVecLin A).toContinuousLinearMap.contDiff

/-- **Derivatives after a linear change of variables**: if the entries of `A` lie in
`[-c₀, c₀]` and all derivatives of order `j` of `f` are bounded by `K`, then those of `f ∘ A` are
bounded by `(d c₀)^j K`. -/
theorem abs_iterDeriv_comp_mulVec_le {A : Mat d} (hA : A.det ≠ 0) {c₀ : ℝ} (hc₀ : 0 ≤ c₀)
    (hA1 : ∀ l i, |A l i| ≤ c₀) {j : ℕ} {f : Vec d → ℝ} (hf : ContDiff ℝ ∞ f) {K : ℝ}
    (hK : ∀ (β : Fin j → Fin d) (x : Vec d), |iterDeriv β f x| ≤ K) (α : Fin j → Fin d)
    (y : Vec d) : |iterDeriv α (fun y => f (A.mulVec y)) y| ≤ ((d : ℝ) * c₀) ^ j * K := by
  induction j generalizing f K with
  | zero => simpa using hK α (A.mulVec y)
  | succ j ih =>
    rw [iterDeriv_succ, coordinateDerivative_comp_mulVec' hA,
      iterDeriv_sum_const_mul Finset.univ (fun l => A l (α 0))
        (fun l => contDiff_comp_mulVec (contDiff_coordinateDerivative hf l) A)]
    have hb : ∀ l, |iterDeriv (Fin.tail α) (fun y => coordinateDerivative l f (A.mulVec y)) y| ≤
        ((d : ℝ) * c₀) ^ j * K := fun l =>
      ih (contDiff_coordinateDerivative hf l) (fun β x => by
        have := hK (Fin.cons l β) x
        rwa [iterDeriv_cons] at this) _
    have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK α y)
    calc |∑ l, A l (α 0) * iterDeriv (Fin.tail α)
          (fun y => coordinateDerivative l f (A.mulVec y)) y|
        ≤ ∑ l, |A l (α 0)| * (((d : ℝ) * c₀) ^ j * K) := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l _ => ?_)
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hb l) (abs_nonneg _)
      _ ≤ ∑ _l : Fin d, c₀ * (((d : ℝ) * c₀) ^ j * K) :=
          Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_right (hA1 l _) (by positivity)
      _ = ((d : ℝ) * c₀) ^ (j + 1) * K := by simp [pow_succ]; ring

/-- A smooth compactly supported function has bounded derivatives of each order. -/
theorem exists_abs_iterDeriv_le {f : Vec d → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (j : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ (β : Fin j → Fin d) (x : Vec d), |iterDeriv β f x| ≤ K := by
  have h : ∀ β : Fin j → Fin d, ∃ K : ℝ, ∀ x, |iterDeriv β f x| ≤ K := fun β => by
    obtain ⟨K, hK⟩ := ((contDiff_iterDeriv β hf).continuous.bounded_above_of_compact_support
      (hasCompactSupport_iterDeriv β hfc))
    exact ⟨K, fun x => by simpa [Real.norm_eq_abs] using hK x⟩
  choose K hK using h
  refine ⟨∑ β, |K β|, Finset.sum_nonneg fun _ _ => abs_nonneg _, fun β x => ?_⟩
  exact (hK β x).trans ((le_abs_self _).trans
    (Finset.single_le_sum (f := fun β => |K β|) (fun _ _ => abs_nonneg _) (Finset.mem_univ β)))

/-! ## The iterated mean value inequality -/

theorem norm_fderiv_le_sum_abs (L : Vec d →L[ℝ] ℝ) :
    ‖L‖ ≤ ∑ i, |L (unitVector i)| := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    fun h => ?_
  have e : L h = ∑ i, h i * L (unitVector i) := by
    have := fderiv_apply_eq_sum_coordinateDerivative (χ := fun y => L y) 0 h
    simpa [coordinateDerivative, ContinuousLinearMap.fderiv] using this
  rw [e, Real.norm_eq_abs, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul, mul_comm]
  exact mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using norm_le_pi_norm h i)
    (abs_nonneg _)

/-- **Lipschitz bound** from bounded coordinate derivatives:
`|f x - f y| ≤ (∑_i B i) |x - y|`. -/
theorem abs_sub_le_of_forall_coordinateDerivative_le {f : Vec d → ℝ} (hf : Differentiable ℝ f)
    {B : Fin d → ℝ} (hB : ∀ i z, |coordinateDerivative i f z| ≤ B i) (x y : Vec d) :
    |f x - f y| ≤ (∑ i, B i) * euclideanNorm (x - y) := by
  have h := (convex_univ : Convex ℝ (Set.univ : Set (Vec d))).norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => hf z) (C := ∑ i, B i) (fun z _ => (norm_fderiv_le_sum_abs _).trans
      (Finset.sum_le_sum fun i _ => hB i z)) (Set.mem_univ y) (Set.mem_univ x)
  rw [Real.norm_eq_abs] at h
  exact h.trans (mul_le_mul_of_nonneg_left (norm_le_euclideanNorm' _)
    (Finset.sum_nonneg fun i _ => (abs_nonneg _).trans (hB i 0)))

/-- **The mean value inequality** on a ball centered at the origin: if the coordinate
derivatives of `f` are bounded by `B i` on `B_t`, then `|f x - f 0| ≤ |x| ∑_i B i` on `B_t`. -/
theorem abs_sub_le_of_coordinateDerivative_le {f : Vec d → ℝ} (hf : Differentiable ℝ f) {t : ℝ}
    {B : Fin d → ℝ}
    (hB : ∀ i y, euclideanNorm y < t → |coordinateDerivative i f y| ≤ B i) {x : Vec d}
    (hx : euclideanNorm x < t) : |f x - f 0| ≤ euclideanNorm x * ∑ i, B i := by
  have hseg : ∀ τ ∈ Set.Icc (0 : ℝ) 1, euclideanNorm (τ • x) < t := fun τ hτ => by
    rw [euclideanNorm_smul_abs, abs_of_nonneg hτ.1]
    calc τ * euclideanNorm x ≤ 1 * euclideanNorm x :=
          mul_le_mul_of_nonneg_right hτ.2 (Real.sqrt_nonneg _)
      _ = euclideanNorm x := one_mul _
      _ < t := hx
  have hderiv : ∀ τ ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt (fun τ : ℝ => f (τ • x))
      (∑ i, x i * coordinateDerivative i f (τ • x)) (Set.Icc 0 1) τ := fun τ _ => by
    have h1 : HasDerivAt (fun τ : ℝ => τ • x) x τ := by
      simpa using (hasDerivAt_id τ).smul_const x
    have h2 := (hf (τ • x)).hasFDerivAt.comp_hasDerivAt τ h1
    rw [fderiv_apply_eq_sum_coordinateDerivative] at h2
    exact h2.hasDerivWithinAt
  have hbound : ∀ τ ∈ Set.Ico (0 : ℝ) 1,
      ‖∑ i, x i * coordinateDerivative i f (τ • x)‖ ≤ euclideanNorm x * ∑ i, B i := by
    intro τ hτ
    rw [Real.norm_eq_abs, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul]
    exact mul_le_mul (abs_apply_le_euclideanNorm x i)
      (hB i _ (hseg τ (Set.Ico_subset_Icc_self hτ))) (abs_nonneg _) (Real.sqrt_nonneg _)
  have h := norm_image_sub_le_of_norm_deriv_le_segment_01' hderiv hbound
  simpa [Real.norm_eq_abs] using h

theorem sum_fin_succ_pi {M : Type*} [AddCommMonoid M] {j : ℕ} (g : (Fin (j + 1) → Fin d) → M) :
    ∑ α, g α = ∑ i, ∑ α : Fin j → Fin d, g (Fin.cons i α) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.consEquiv fun _ => Fin d).symm _ _ fun α => by
    simp [Fin.consEquiv]).trans rfl

theorem mul_sum_range_pow (n : ℕ) (t : ℝ) (X : Fin d → ℕ → ℝ) :
    t * ∑ i, ∑ j ∈ Finset.range n, t ^ j * X i j =
      ∑ j ∈ Finset.range n, t ^ (j + 1) * ∑ i, X i j := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

/-- **The iterated mean value inequality**: if the derivatives `∂^β f` of order `n` are bounded
by `A β` on `B_t`, then on `B_t`,
`|f x| ≤ ∑_{j < n} t^j ∑_{α of order j} |∂^α f(0)| + t^n ∑_β A β`. -/
theorem abs_le_of_iterDeriv_le {f : Vec d → ℝ} (hf : ContDiff ℝ ∞ f) {t : ℝ} (n : ℕ)
    {A : (Fin n → Fin d) → ℝ}
    (hA : ∀ (β : Fin n → Fin d) (y : Vec d), euclideanNorm y < t → |iterDeriv β f y| ≤ A β)
    {x : Vec d} (hx : euclideanNorm x < t) :
    |f x| ≤ ∑ j ∈ Finset.range n, t ^ j * ∑ α : Fin j → Fin d, |iterDeriv α f 0| +
      t ^ n * ∑ β, A β := by
  induction n generalizing f x with
  | zero =>
    simpa [Finset.univ_unique] using hA default x hx
  | succ n ih =>
    have ht : 0 ≤ t := (Real.sqrt_nonneg _).trans hx.le
    set B : Fin d → ℝ := fun i => ∑ j ∈ Finset.range n, t ^ j *
        ∑ α : Fin j → Fin d, |iterDeriv α (coordinateDerivative i f) 0| +
      t ^ n * ∑ β : Fin n → Fin d, A (Fin.cons i β) with hBdef
    have hB : ∀ i y, euclideanNorm y < t → |coordinateDerivative i f y| ≤ B i := fun i y hy =>
      ih (contDiff_coordinateDerivative hf i) (fun β y hy => by
        have := hA (Fin.cons i β) y hy
        rwa [iterDeriv_cons] at this) hy
    have hmv := abs_sub_le_of_coordinateDerivative_le (hf.differentiable (by simp)) hB hx
    have h0t : euclideanNorm (0 : Vec d) < t := by
      have : euclideanNorm (0 : Vec d) = 0 := by simp [euclideanNorm, euclideanSq, dot]
      rw [this]
      exact lt_of_le_of_lt (Real.sqrt_nonneg _) hx
    have hB0 : 0 ≤ ∑ i, B i := Finset.sum_nonneg fun i _ => (abs_nonneg _).trans (hB i 0 h0t)
    have h1 : |f x| ≤ |f 0| + t * ∑ i, B i := by
      have := abs_sub_abs_le_abs_sub (f x) (f 0)
      have h2 : euclideanNorm x * ∑ i, B i ≤ t * ∑ i, B i :=
        mul_le_mul_of_nonneg_right hx.le hB0
      linarith
    refine h1.trans (le_of_eq ?_)
    rw [Finset.sum_range_succ', pow_zero, one_mul]
    have e0 : ∑ α : Fin 0 → Fin d, |iterDeriv α f 0| = |f 0| := by
      simp [Finset.univ_unique]
    rw [e0]
    have e1 : ∀ j, ∑ α : Fin (j + 1) → Fin d, |iterDeriv α f 0| =
        ∑ i, ∑ α : Fin j → Fin d, |iterDeriv α (coordinateDerivative i f) 0| := fun j => by
      rw [sum_fin_succ_pi]
      simp only [iterDeriv_cons]
    have e2 : ∑ β : Fin (n + 1) → Fin d, A β = ∑ i, ∑ β : Fin n → Fin d, A (Fin.cons i β) :=
      sum_fin_succ_pi A
    simp only [e1, e2]
    have hsplit : t * ∑ i, B i = ∑ j ∈ Finset.range n, t ^ (j + 1) *
          ∑ i, ∑ α : Fin j → Fin d, |iterDeriv α (coordinateDerivative i f) 0| +
        t ^ (n + 1) * ∑ i, ∑ β : Fin n → Fin d, A (Fin.cons i β) := by
      simp only [hBdef, Finset.sum_add_distrib, mul_add]
      rw [mul_sum_range_pow n t (fun i j => ∑ α : Fin j → Fin d,
        |iterDeriv α (coordinateDerivative i f) 0|)]
      congr 1
      rw [Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hsplit]
    ring

end QSH
