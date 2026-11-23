import QuantitativeStochasticHomogenization.AppD.HeatEquation
import QuantitativeStochasticHomogenization.AppD.HeatSemigroupDerivatives
import QuantitativeStochasticHomogenization.Ch04.Sec05.GaussianMasses
import QuantitativeStochasticHomogenization.Ch04.Sec01.Proposition43
import QuantitativeStochasticHomogenization.Ch03.Sec03.TestMollification

/-!
# Anisotropic Gaussians in an orthonormal frame

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 4.3, the heat identity (H) of the route of Proposition 4.10.

For an orthogonal matrix `Q` and times `t_k > 0`, the anisotropic Gaussian with covariance
`2 Qᵀ diag(t) Q` is `x ↦ ∏_k Φ₁(t_k, (Q x)_k)`. Its derivatives of order at most two in each
coordinate of the frame are of the same form, with the one-dimensional kernels `Φ₁`,
`-(y/2t) Φ₁` and `(y²/4t² - 1/2t) Φ₁` (`heatKernel1D`, `anisoKernel`, `rotKernel`). Proved here:

* the derivatives of `y ↦ ∏_k Φ₁^{(n_k)}(t_k, (Q(z - y))_k)` in space (`fderiv_rotKernel_apply`)
  and of `u ↦ ∏_k Φ₁(t_k(u), w_k)` in time along affine times (`hasDerivAt_anisoKernel_time`);
* Gaussian majorants uniform for times in a compact interval (`exists_abs_anisoKernel_le`), and
  the majorant of the zeroth order kernel (`anisoKernel_zero_le`);
* the semigroup splitting with the isotropic heat kernel, with up to two derivatives,
  `∫ Φ^{(n)}_e(Q x) Φ(u, v - x) dx = Φ^{(n)}_{e + u}(Q v)` (`integral_rotKernel_mul_heatKernel`);
* the bound of the Hessian contracted with two vectors,
  `|∑_{k,m} a_k c_m ∂_k ∂_m Φ_e(w)| ≤ (2K + 1/2) u⁻¹ (2K)^{d/2} Φ(2Ku, w) |a| |c|` for
  `u ≤ e_k ≤ K u` (`abs_hessian_anisoKernel_le`), and of the gradient contracted with a vector,
  `|∑_k a_k ∂_k Φ_b(w)| ≤ (4πβ₁)^{-d/2} (√(8β₂)/(2β₁)) e^{-|w|²/(8β₂)} |a|` for
  `β₁ ≤ b_k ≤ β₂` (`abs_gradient_anisoKernel_le`).
-/

open MeasureTheory Filter Set
open scoped ContDiff Topology Matrix

noncomputable section

namespace QSH

/-! ## The one-dimensional kernels -/

/-- The polynomial factors of `Φ₁`, `∂_y Φ₁` and `∂_y² Φ₁`. -/
def heatPoly : ℕ → ℝ → ℝ → ℝ
  | 0, _, _ => 1
  | 1, t, y => -(y / (2 * t))
  | _ + 2, t, y => heatFactor t y

/-- `Φ₁(t, y)` for `n = 0`, `∂_y Φ₁(t, y)` for `n = 1` and `∂_y² Φ₁(t, y)` for `n ≥ 2`. -/
def heatKernel1D (n : ℕ) (t y : ℝ) : ℝ := heatPoly n t y * heatKernel1 t y

theorem heatKernel1D_zero (t y : ℝ) : heatKernel1D 0 t y = heatKernel1 t y := by
  simp [heatKernel1D, heatPoly]

theorem heatKernel1D_one (t y : ℝ) : heatKernel1D 1 t y = -(y / (2 * t)) * heatKernel1 t y := by
  simp [heatKernel1D, heatPoly]

theorem heatKernel1D_two (t y : ℝ) : heatKernel1D 2 t y = heatFactor t y * heatKernel1 t y := by
  simp [heatKernel1D, heatPoly]

theorem hasDerivAt_heatKernel1D {n : ℕ} (hn : n ≤ 1) {t : ℝ} (ht : 0 < t) (y : ℝ) :
    HasDerivAt (heatKernel1D n t) (heatKernel1D (n + 1) t y) y := by
  interval_cases n
  · have h : heatKernel1D 0 t = heatKernel1 t := funext fun y => heatKernel1D_zero t y
    rw [h, zero_add, heatKernel1D_one]
    exact hasDerivAt_heatKernel1_space ht y
  · have h : heatKernel1D 1 t = deriv (heatKernel1 t) := by
      rw [deriv_heatKernel1 ht]
      funext y
      exact heatKernel1D_one t y
    rw [h, show 1 + 1 = 2 from rfl, heatKernel1D_two]
    exact hasDerivAt_deriv_heatKernel1 ht y

theorem contDiff_heatKernel1D (n : ℕ) (t : ℝ) : ContDiff ℝ ∞ (heatKernel1D n t) := by
  have h : heatKernel1D n t = fun y => heatPoly n t y * heatKernel1 t y := rfl
  rw [h]
  refine ContDiff.mul ?_ (contDiff_heatKernel1 t)
  rcases n with _ | _ | n
  · exact contDiff_const
  · exact (contDiff_id.div_const _).neg
  · change ContDiff ℝ ∞ fun y => heatFactor t y
    unfold heatFactor
    exact ((contDiff_id.pow 2).div_const _).sub contDiff_const

theorem measurable_heatKernel1D (n : ℕ) :
    Measurable fun p : ℝ × ℝ => heatKernel1D n p.1 p.2 := by
  have hk : Measurable fun p : ℝ × ℝ => heatKernel1 p.1 p.2 := by
    unfold heatKernel1
    exact ((measurable_const.mul measurable_fst).pow_const _).mul
      (Real.continuous_exp.measurable.comp
        ((measurable_snd.mul measurable_snd).neg.div (measurable_const.mul measurable_fst)))
  refine Measurable.mul ?_ hk
  rcases n with _ | _ | n
  · exact measurable_const
  · exact (measurable_snd.div (measurable_const.mul measurable_fst)).neg
  · change Measurable fun p : ℝ × ℝ => heatFactor p.1 p.2
    unfold heatFactor
    exact ((measurable_snd.pow_const 2).div
      (measurable_const.mul (measurable_fst.pow_const 2))).sub
      (measurable_const.div (measurable_const.mul measurable_fst))

theorem heatKernel1_pos {t : ℝ} (ht : 0 < t) (y : ℝ) : 0 < heatKernel1 t y := by
  unfold heatKernel1
  exact mul_pos (Real.rpow_pos_of_pos (by positivity) _) (Real.exp_pos _)

/-- `Φ₁(t, y) ≤ (4πτ₁)^{-1/2} e^{-y²/(4τ₂)}` for `τ₁ ≤ t ≤ τ₂`. -/
theorem heatKernel1_le {τ₁ τ₂ t : ℝ} (hτ₁ : 0 < τ₁) (h₁ : τ₁ ≤ t) (h₂ : t ≤ τ₂) (y : ℝ) :
    heatKernel1 t y ≤ (4 * Real.pi * τ₁) ^ (-(1 : ℝ) / 2) * Real.exp (-(y * y) / (4 * τ₂)) := by
  have ht : 0 < t := hτ₁.trans_le h₁
  unfold heatKernel1
  refine mul_le_mul ?_ ?_ (Real.exp_pos _).le (by positivity)
  · exact Real.rpow_le_rpow_of_nonpos (by positivity) (by nlinarith [Real.pi_pos]) (by norm_num)
  · refine Real.exp_le_exp.mpr ?_
    rw [neg_div, neg_div, neg_le_neg_iff]
    exact div_le_div_of_nonneg_left (mul_self_nonneg y) (by positivity) (by linarith)

theorem mul_exp_neg_le_one (s : ℝ) : s * Real.exp (-s) ≤ 1 := by
  have h := Real.add_one_le_exp s
  have : s ≤ Real.exp s := by linarith
  calc s * Real.exp (-s) ≤ Real.exp s * Real.exp (-s) :=
        mul_le_mul_of_nonneg_right this (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]

theorem abs_heatPoly_le {n : ℕ} {τ₁ t : ℝ} (hτ₁ : 0 < τ₁) (h₁ : τ₁ ≤ t) (y : ℝ) :
    |heatPoly n t y| ≤ 1 + |y| / (2 * τ₁) + (y * y / (4 * τ₁ ^ 2) + 1 / (2 * τ₁)) := by
  have ht : 0 < t := hτ₁.trans_le h₁
  have h2t : 2 * τ₁ ≤ 2 * t := by linarith
  have hyt : |y| / (2 * t) ≤ |y| / (2 * τ₁) :=
    div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) h2t
  have hyy : y ^ 2 / (4 * t ^ 2) ≤ y * y / (4 * τ₁ ^ 2) := by
    rw [sq y]
    exact div_le_div_of_nonneg_left (mul_self_nonneg y) (by positivity) (by nlinarith)
  have hit : 1 / (2 * t) ≤ 1 / (2 * τ₁) :=
    div_le_div_of_nonneg_left zero_le_one (by positivity) h2t
  have h0 : 0 ≤ |y| / (2 * τ₁) := by positivity
  have h0' : 0 ≤ y * y / (4 * τ₁ ^ 2) + 1 / (2 * τ₁) :=
    add_nonneg (div_nonneg (mul_self_nonneg y) (by positivity)) (by positivity)
  rcases n with _ | _ | n
  · simp only [heatPoly, abs_one]
    linarith
  · simp only [heatPoly]
    rw [abs_neg, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * t)]
    linarith
  · simp only [heatPoly, heatFactor]
    refine (abs_sub _ _).trans ?_
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    linarith

/-- **Uniform Gaussian majorant** of the one-dimensional kernels for times in `[τ₁, τ₂]`. -/
theorem exists_abs_heatKernel1D_le (n : ℕ) {τ₁ τ₂ : ℝ} (hτ₁ : 0 < τ₁) (hτ : τ₁ ≤ τ₂) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, τ₁ ≤ t → t ≤ τ₂ → ∀ y : ℝ,
      |heatKernel1D n t y| ≤ B * Real.exp (-(y * y) / (8 * τ₂)) := by
  have hτ₂ : 0 < τ₂ := hτ₁.trans_le hτ
  set c : ℝ := (4 * Real.pi * τ₁) ^ (-(1 : ℝ) / 2) with hc
  have hc0 : 0 ≤ c := by positivity
  set p : ℝ := 1 + 1 / (2 * τ₁) + (1 / (2 * τ₁) + 1 / (4 * τ₁ ^ 2)) * (1 + 8 * τ₂) with hp
  have hp0 : 0 ≤ p := by rw [hp]; positivity
  refine ⟨c * p, mul_nonneg hc0 hp0, fun t h₁ h₂ y => ?_⟩
  have ht : 0 < t := hτ₁.trans_le h₁
  set E := Real.exp (-(y * y) / (8 * τ₂)) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hyy0 : 0 ≤ y * y / (8 * τ₂) := div_nonneg (mul_self_nonneg y) (by positivity)
  have hE1 : E ≤ 1 := by
    rw [hE, Real.exp_le_one_iff, neg_div]
    exact neg_nonpos.mpr hyy0
  have hy2 : y * y * E ≤ 8 * τ₂ := by
    have h := mul_exp_neg_le_one (y * y / (8 * τ₂))
    rw [show -(y * y / (8 * τ₂)) = -(y * y) / (8 * τ₂) by ring, ← hE] at h
    have h' : y * y * E = 8 * τ₂ * (y * y / (8 * τ₂) * E) := by
      field_simp
    rw [h']
    nlinarith
  have hy1 : |y| ≤ 1 + y * y := by
    rcases le_or_gt |y| 1 with h | h
    · nlinarith [mul_self_nonneg y]
    · have : |y| ≤ |y| * |y| := by nlinarith
      rw [abs_mul_abs_self] at this
      linarith
  have hyE : |y| * E ≤ 1 + 8 * τ₂ := by nlinarith
  have hE2 : Real.exp (-(y * y) / (4 * τ₂)) = E * E := by
    rw [hE, ← Real.exp_add]
    congr 1
    field_simp
    ring
  have hk := heatKernel1_le hτ₁ h₁ h₂ y
  have hpoly := abs_heatPoly_le (n := n) hτ₁ h₁ y
  have ha : 0 ≤ 1 / (2 * τ₁) := by positivity
  have hb : 0 ≤ 1 / (4 * τ₁ ^ 2) := by positivity
  have hpE : |heatPoly n t y| * E ≤ p := by
    calc |heatPoly n t y| * E
        ≤ (1 + |y| / (2 * τ₁) + (y * y / (4 * τ₁ ^ 2) + 1 / (2 * τ₁))) * E :=
          mul_le_mul_of_nonneg_right hpoly hE0.le
      _ = (1 + 1 / (2 * τ₁)) * E + 1 / (2 * τ₁) * (|y| * E) +
            1 / (4 * τ₁ ^ 2) * (y * y * E) := by ring
      _ ≤ (1 + 1 / (2 * τ₁)) * 1 + 1 / (2 * τ₁) * (1 + 8 * τ₂) +
            1 / (4 * τ₁ ^ 2) * (8 * τ₂) := by gcongr
      _ ≤ p := by rw [hp]; nlinarith
  unfold heatKernel1D
  rw [abs_mul, abs_of_pos (heatKernel1_pos ht y)]
  calc |heatPoly n t y| * heatKernel1 t y ≤ |heatPoly n t y| * (c * (E * E)) := by
        rw [← hE2]
        exact mul_le_mul_of_nonneg_left hk (abs_nonneg _)
    _ = c * E * (|heatPoly n t y| * E) := by ring
    _ ≤ c * E * p := mul_le_mul_of_nonneg_left hpE (by positivity)
    _ = c * p * E := by ring

/-! ## Products in an orthonormal frame -/

variable {d : ℕ}

/-- `∏_k Φ₁^{(n_k)}(t_k, w_k)`: the anisotropic Gaussian with times `t_k` along the coordinate
axes, differentiated `n_k` times in the `k`-th coordinate. -/
def anisoKernel (t : Fin d → ℝ) (n : Fin d → ℕ) (w : Vec d) : ℝ :=
  prodFun (fun k => heatKernel1D (n k) (t k)) w

/-- The anisotropic Gaussian in the frame `Q`, centered at `z`:
`y ↦ ∏_k Φ₁^{(n_k)}(t_k, (Q(z - y))_k)`. -/
def rotKernel (Q : Mat d) (t : Fin d → ℝ) (n : Fin d → ℕ) (z y : Vec d) : ℝ :=
  anisoKernel t n (Q *ᵥ (z - y))

theorem continuous_mulVec (Q : Mat d) : Continuous fun x : Vec d => Q *ᵥ x :=
  Continuous.matrix_mulVec continuous_const continuous_id

theorem contDiff_mulVec (Q : Mat d) : ContDiff ℝ ∞ fun x : Vec d => Q *ᵥ x :=
  (LinearMap.toContinuousLinearMap (Matrix.mulVecLin Q)).contDiff

theorem contDiff_anisoKernel (t : Fin d → ℝ) (n : Fin d → ℕ) :
    ContDiff ℝ ∞ (anisoKernel t n) := by
  show ContDiff ℝ ∞ (fun w : Vec d => ∏ k, heatKernel1D (n k) (t k) (w k))
  exact contDiff_prod fun k _ => (contDiff_heatKernel1D (n k) (t k)).comp (contDiff_apply ℝ ℝ k)

theorem contDiff_rotKernel (Q : Mat d) (t : Fin d → ℝ) (n : Fin d → ℕ) (z : Vec d) :
    ContDiff ℝ ∞ (rotKernel Q t n z) := by
  unfold rotKernel
  exact (contDiff_anisoKernel t n).comp ((contDiff_mulVec Q).comp (contDiff_const.sub contDiff_id))

theorem measurable_anisoKernel_uncurry (n : Fin d → ℕ) :
    Measurable fun p : (Fin d → ℝ) × Vec d => anisoKernel p.1 n p.2 := by
  show Measurable fun p : (Fin d → ℝ) × Vec d => ∏ k, heatKernel1D (n k) (p.1 k) (p.2 k)
  refine Finset.measurable_prod _ fun k _ => ?_
  have hf : Measurable fun p : (Fin d → ℝ) × Vec d => (p.1 k, p.2 k) :=
    ((measurable_pi_apply k).comp measurable_fst).prodMk ((measurable_pi_apply k).comp measurable_snd)
  exact (measurable_heatKernel1D (n k)).comp hf

theorem anisoKernel_eq_mul (t : Fin d → ℝ) (n : Fin d → ℕ) (w : Vec d) :
    anisoKernel t n w = (∏ k, heatPoly (n k) (t k) (w k)) * anisoKernel t 0 w := by
  simp only [anisoKernel, prodFun]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [heatKernel1D, Pi.zero_apply, heatKernel1D_zero]

theorem anisoKernel_zero_pos {t : Fin d → ℝ} (ht : ∀ k, 0 < t k) (w : Vec d) :
    0 < anisoKernel t 0 w := by
  simp only [anisoKernel, prodFun]
  exact Finset.prod_pos fun k _ => by
    rw [Pi.zero_apply, heatKernel1D_zero]
    exact heatKernel1_pos (ht k) _

theorem anisoKernel_const_eq {s : ℝ} (hs : 0 < s) (w : Vec d) :
    anisoKernel (fun _ => s) 0 w = euclideanHeatKernel s w := by
  rw [euclideanHeatKernel_eq_prodFun hs]
  simp only [anisoKernel, prodFun]
  exact Finset.prod_congr rfl fun k _ => by rw [Pi.zero_apply, heatKernel1D_zero]

/-- The coordinate derivatives of the products. -/
theorem coordinateDerivative_anisoKernel {t : Fin d → ℝ} (ht : ∀ k, 0 < t k) {n : Fin d → ℕ}
    {j : Fin d} (hn : n j ≤ 1) (w : Vec d) :
    coordinateDerivative j (anisoKernel t n) w = anisoKernel t (n + Pi.single j 1) w := by
  classical
  unfold anisoKernel
  rw [coordinateDerivative_prodFun (fun k => (contDiff_heatKernel1D (n k) (t k)).differentiable
    (by simp)) j w]
  unfold prodFun
  refine Finset.prod_congr rfl fun k _ => ?_
  by_cases hkj : k = j
  · subst hkj
    simp only [Function.update_self, Pi.add_apply, Pi.single_eq_same]
    exact (hasDerivAt_heatKernel1D hn (ht _) _).deriv
  · rw [Function.update_of_ne hkj]
    simp [hkj]

theorem fderiv_anisoKernel_apply {t : Fin d → ℝ} (ht : ∀ k, 0 < t k) {n : Fin d → ℕ}
    (hn : ∀ k, n k ≤ 1) (w v : Vec d) :
    fderiv ℝ (anisoKernel t n) w v = ∑ j, v j * anisoKernel t (n + Pi.single j 1) w := by
  rw [fderiv_apply_eq_sum_coordinateDerivative (χ := anisoKernel t n) w v]
  exact Finset.sum_congr rfl fun j _ => by rw [coordinateDerivative_anisoKernel ht (hn j)]

/-- **The space derivative of the rotated products**:
`D_v [y ↦ Φ^{(n)}_t(Q(z - y))] = -∑_j (Qv)_j Φ^{(n + e_j)}_t(Q(z - y))` for `n ≤ 1`. -/
theorem fderiv_rotKernel_apply (Q : Mat d) {t : Fin d → ℝ} (ht : ∀ k, 0 < t k) {n : Fin d → ℕ}
    (hn : ∀ k, n k ≤ 1) (z y v : Vec d) :
    fderiv ℝ (rotKernel Q t n z) y v =
      -∑ j, (Q *ᵥ v) j * rotKernel Q t (n + Pi.single j 1) z y := by
  set L : Vec d →L[ℝ] Vec d := LinearMap.toContinuousLinearMap (Matrix.mulVecLin Q) with hL
  have hLv : ∀ x, L x = Q *ᵥ x := fun x => rfl
  have hA : HasFDerivAt (fun y => L (z - y)) (L.comp (-(ContinuousLinearMap.id ℝ (Vec d)))) y :=
    L.hasFDerivAt.comp y ((hasFDerivAt_id y).const_sub z)
  have hP : HasFDerivAt (anisoKernel t n) (fderiv ℝ (anisoKernel t n) (L (z - y))) (L (z - y)) :=
    ((contDiff_anisoKernel t n).differentiable (by simp) _).hasFDerivAt
  have h := hP.comp y hA
  have heq : rotKernel Q t n z = (anisoKernel t n) ∘ fun y => L (z - y) := by
    funext y
    simp only [rotKernel, Function.comp_apply, hLv]
  have key : fderiv ℝ (rotKernel Q t n z) y v =
      fderiv ℝ (anisoKernel t n) (Q *ᵥ (z - y)) (-(Q *ᵥ v)) := by
    rw [heq, h.fderiv]
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, neg_apply,
      ContinuousLinearMap.id_apply, map_neg, hLv]
    rw [Matrix.mulVec_neg, map_neg]
  rw [key, fderiv_anisoKernel_apply ht hn, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.neg_apply, neg_mul]
  rfl

/-- The gradient of the rotated products. -/
theorem gradient_rotKernel (Q : Mat d) {t : Fin d → ℝ} (ht : ∀ k, 0 < t k) {n : Fin d → ℕ}
    (hn : ∀ k, n k ≤ 1) (z y : Vec d) (i : Fin d) :
    gradient (rotKernel Q t n z) y i =
      -∑ j, Q j i * rotKernel Q t (n + Pi.single j 1) z y := by
  rw [gradient, coordinateDerivative, fderiv_rotKernel_apply Q ht hn]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  simp [Matrix.mulVec, dotProduct, unitVector, Pi.single_apply]

/-! ## The time derivative -/

theorem hasDerivAt_anisoKernel_time {α β : Fin d → ℝ} {u : ℝ} (hpos : ∀ k, 0 < α k + β k * u)
    (w : Vec d) :
    HasDerivAt (fun u => anisoKernel (fun k => α k + β k * u) 0 w)
      (∑ m, β m * anisoKernel (fun k => α k + β k * u) (Pi.single m 2) w) u := by
  classical
  have hf : ∀ m ∈ (Finset.univ : Finset (Fin d)),
      HasDerivAt (fun u => heatKernel1 (α m + β m * u) (w m))
        (heatFactor (α m + β m * u) (w m) * heatKernel1 (α m + β m * u) (w m) * β m) u := by
    intro m _
    have h1 : HasDerivAt (fun u => α m + β m * u) (β m) u := by
      simpa using ((hasDerivAt_id u).const_mul (β m)).const_add (α m)
    exact (hasDerivAt_heatKernel1_time (hpos m) (w m)).comp u h1
  have hp := HasDerivAt.fun_finsetProd hf
  have hfun : (fun u => anisoKernel (fun k => α k + β k * u) 0 w) =
      fun u => ∏ m, heatKernel1 (α m + β m * u) (w m) := by
    funext u
    simp only [anisoKernel, prodFun]
    exact Finset.prod_congr rfl fun m _ => by rw [Pi.zero_apply, heatKernel1D_zero]
  rw [hfun]
  refine hp.congr_deriv (Finset.sum_congr rfl fun m _ => ?_)
  simp only [anisoKernel, prodFun]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ m), Pi.single_eq_same,
    heatKernel1D_two, smul_eq_mul]
  have hrest : ∏ k ∈ Finset.univ.erase m,
      heatKernel1D ((Pi.single m 2 : Fin d → ℕ) k) (α k + β k * u) (w k) =
      ∏ k ∈ Finset.univ.erase m, heatKernel1 (α k + β k * u) (w k) :=
    Finset.prod_congr rfl fun k hk => by
      rw [Pi.single_eq_of_ne (Finset.ne_of_mem_erase hk), heatKernel1D_zero]
  rw [hrest]
  ring

/-! ## Orthogonal frames -/

theorem euclideanSq_mulVec_of_orthogonal {Q : Mat d} (hQ : Q.transpose * Q = 1) (x : Vec d) :
    euclideanSq (Q *ᵥ x) = euclideanSq x := by
  unfold euclideanSq dot
  change (Q *ᵥ x) ⬝ᵥ (Q *ᵥ x) = x ⬝ᵥ x
  rw [Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, Matrix.vecMul_vecMul, hQ,
    Matrix.vecMul_one]

theorem euclideanNorm_mulVec_of_orthogonal {Q : Mat d} (hQ : Q.transpose * Q = 1) (x : Vec d) :
    euclideanNorm (Q *ᵥ x) = euclideanNorm x := by
  unfold euclideanNorm
  rw [euclideanSq_mulVec_of_orthogonal hQ]

theorem euclideanHeatKernel_mulVec_of_orthogonal {Q : Mat d} (hQ : Q.transpose * Q = 1) (s : ℝ)
    (x : Vec d) : euclideanHeatKernel s (Q *ᵥ x) = euclideanHeatKernel s x := by
  unfold euclideanHeatKernel
  rw [euclideanSq_mulVec_of_orthogonal hQ]

/-- The rotation `x ↦ Q x` as a homeomorphism. -/
def orthogonalHomeomorph {Q : Mat d} (hQ : Q.transpose * Q = 1) : Vec d ≃ₜ Vec d where
  toFun x := Q *ᵥ x
  invFun y := Q.transpose *ᵥ y
  left_inv x := by simp only [Matrix.mulVec_mulVec, hQ, Matrix.one_mulVec]
  right_inv y := by
    have hQ' : Q * Q.transpose = 1 := mul_eq_one_comm.mp hQ
    simp only [Matrix.mulVec_mulVec, hQ', Matrix.one_mulVec]
  continuous_toFun := continuous_mulVec Q
  continuous_invFun := continuous_mulVec Q.transpose

theorem measurePreserving_mulVec_of_orthogonal {Q : Mat d} (hQ : Q.transpose * Q = 1) :
    MeasurePreserving (fun x : Vec d => Q *ᵥ x) volume volume := by
  classical
  have hdet : Q.det * Q.det = 1 := by
    have h := congrArg Matrix.det hQ
    rwa [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
  have hdet0 : Q.det ≠ 0 := fun h => by rw [h, zero_mul] at hdet; exact zero_ne_one hdet
  have habs : |(Q.det)⁻¹| = 1 := by
    have h1 : |Q.det| * |Q.det| = 1 := by rw [← abs_mul, hdet, abs_one]
    have h2 : |Q.det| = 1 := by nlinarith [abs_nonneg Q.det]
    rw [abs_inv, h2, inv_one]
  refine ⟨(continuous_mulVec Q).measurable, ?_⟩
  have h := Real.map_matrix_volume_pi_eq_smul_volume_pi hdet0
  rw [habs, ENNReal.ofReal_one, one_smul] at h
  have hf : (⇑(Matrix.toLin' Q) : Vec d → Vec d) = fun x => Q *ᵥ x :=
    funext fun x => Matrix.toLin'_apply Q x
  rw [hf] at h
  exact h

theorem integral_comp_mulVec_of_orthogonal {Q : Mat d} (hQ : Q.transpose * Q = 1)
    (g : Vec d → ℝ) : ∫ x, g (Q *ᵥ x) = ∫ y, g y :=
  (measurePreserving_mulVec_of_orthogonal hQ).integral_comp
    (orthogonalHomeomorph hQ).measurableEmbedding g

/-- `e^{-|w|²/(4s)} = (4πs)^{d/2} Φ(s, w)`. -/
theorem exp_neg_euclideanSq_eq {s : ℝ} (hs : 0 < s) (w : Vec d) :
    Real.exp (-euclideanSq w / (4 * s)) =
      (4 * Real.pi * s) ^ ((d : ℝ) / 2) * euclideanHeatKernel s w := by
  unfold euclideanHeatKernel
  rw [← mul_assoc, ← Real.rpow_add (by positivity), show (d : ℝ) / 2 + -(d : ℝ) / 2 = 0 by ring,
    Real.rpow_zero, one_mul]

theorem prod_exp_neg_sq_eq (c : ℝ) (w : Vec d) :
    ∏ k, Real.exp (-(w k * w k) / c) = Real.exp (-euclideanSq w / c) := by
  rw [← Real.exp_sum]
  congr 1
  simp only [euclideanSq, dot, neg_div, Finset.sum_div, Finset.sum_neg_distrib]

/-! ## Majorants -/

/-- **Uniform Gaussian majorant of the products** for times in `[τ₁, τ₂]`. -/
theorem exists_abs_anisoKernel_le (n : Fin d → ℕ) {τ₁ τ₂ : ℝ} (hτ₁ : 0 < τ₁) (hτ : τ₁ ≤ τ₂) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : Fin d → ℝ, (∀ k, τ₁ ≤ t k ∧ t k ≤ τ₂) → ∀ w : Vec d,
      |anisoKernel t n w| ≤ B * euclideanHeatKernel (2 * τ₂) w := by
  have hτ₂ : 0 < τ₂ := hτ₁.trans_le hτ
  have hb := fun k => exists_abs_heatKernel1D_le (n k) hτ₁ hτ
  choose B hB0 hB using hb
  refine ⟨(∏ k, B k) * (4 * Real.pi * (2 * τ₂)) ^ ((d : ℝ) / 2),
    mul_nonneg (Finset.prod_nonneg fun k _ => hB0 k) (by positivity), fun t ht w => ?_⟩
  simp only [anisoKernel, prodFun]
  rw [Finset.abs_prod, mul_assoc, ← exp_neg_euclideanSq_eq (by positivity),
    show 4 * (2 * τ₂) = 8 * τ₂ by ring, ← prod_exp_neg_sq_eq, ← Finset.prod_mul_distrib]
  exact Finset.prod_le_prod₀ (fun k _ => abs_nonneg _)
    fun k _ => hB k (t k) (ht k).1 (ht k).2 (w k)

/-- The products are bounded. -/
theorem exists_abs_anisoKernel_le_const {t : Fin d → ℝ} (ht : ∀ k, 0 < t k) (n : Fin d → ℕ) :
    ∃ C : ℝ, ∀ w : Vec d, |anisoKernel t n w| ≤ C := by
  have hb := fun k => exists_abs_heatKernel1D_le (n k) (ht k) le_rfl
  choose B hB0 hB using hb
  refine ⟨∏ k, B k, fun w => ?_⟩
  simp only [anisoKernel, prodFun]
  rw [Finset.abs_prod]
  refine Finset.prod_le_prod₀ (fun k _ => abs_nonneg _) fun k _ => ?_
  refine (hB k (t k) le_rfl le_rfl (w k)).trans ?_
  have h1 : Real.exp (-(w k * w k) / (8 * t k)) ≤ 1 := by
    rw [Real.exp_le_one_iff, neg_div]
    exact neg_nonpos.mpr (div_nonneg (mul_self_nonneg _) (by linarith [ht k]))
  calc B k * Real.exp (-(w k * w k) / (8 * t k)) ≤ B k * 1 :=
        mul_le_mul_of_nonneg_left h1 (hB0 k)
    _ = B k := mul_one _

/-- `Φ_t(w) ≤ (4πτ₁)^{-d/2} e^{-|w|²/(4τ₂)}` for `τ₁ ≤ t_k ≤ τ₂`. -/
theorem anisoKernel_zero_le {τ₁ τ₂ : ℝ} (hτ₁ : 0 < τ₁) {t : Fin d → ℝ}
    (ht : ∀ k, τ₁ ≤ t k ∧ t k ≤ τ₂) (w : Vec d) :
    anisoKernel t 0 w ≤
      (4 * Real.pi * τ₁) ^ (-(d : ℝ) / 2) * Real.exp (-euclideanSq w / (4 * τ₂)) := by
  simp only [anisoKernel, prodFun]
  rw [← prod_exp_neg_sq_eq, show -(d : ℝ) / 2 = (-(1 : ℝ) / 2) * (d : ℝ) by ring,
    Real.rpow_mul (by positivity), Real.rpow_natCast,
    ← Fin.prod_const d ((4 * Real.pi * τ₁) ^ (-(1 : ℝ) / 2)), ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod₀ (fun k _ => ?_) fun k _ => ?_
  · rw [Pi.zero_apply, heatKernel1D_zero]
    exact (heatKernel1_pos (hτ₁.trans_le (ht k).1) _).le
  · rw [Pi.zero_apply, heatKernel1D_zero]
    exact heatKernel1_le hτ₁ (ht k).1 (ht k).2 (w k)

/-! ## The semigroup splitting -/

theorem integral_heatKernel1_sub_mul {e u : ℝ} (he : 0 < e) (hu : 0 < u) (w : ℝ) :
    ∫ y, heatKernel1 e (w - y) * heatKernel1 u y = heatKernel1 (e + u) w := by
  have h := integral_exp_sub_sq_mul_exp_sub_sq he hu w 0
  simp only [sub_zero] at h
  have hA : 0 < 4 * Real.pi * e := by positivity
  have hB : 0 < 4 * Real.pi * u := by positivity
  have hC : 0 < 4 * Real.pi * (e + u) := by positivity
  have hfun : (fun y => heatKernel1 e (w - y) * heatKernel1 u y) = fun y =>
      ((4 * Real.pi * e) ^ (-(1 : ℝ) / 2) * (4 * Real.pi * u) ^ (-(1 : ℝ) / 2)) *
        (Real.exp (-((w - y) * (w - y)) / (4 * e)) * Real.exp (-(y * y) / (4 * u))) := by
    funext y
    unfold heatKernel1
    ring
  rw [hfun, integral_const_mul, h]
  unfold heatKernel1
  rw [← mul_assoc]
  congr 1
  rw [show Real.pi / ((e + u) / (4 * e * u)) =
      (4 * Real.pi * e) * (4 * Real.pi * u) / (4 * Real.pi * (e + u)) by field_simp,
    Real.sqrt_eq_rpow, Real.div_rpow (by positivity) hC.le, Real.mul_rpow hA.le hB.le,
    show -(1 : ℝ) / 2 = -(1 / 2) by ring, Real.rpow_neg hA.le, Real.rpow_neg hB.le,
    Real.rpow_neg hC.le]
  have hA' : 0 < (4 * Real.pi * e) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hA _
  have hB' : 0 < (4 * Real.pi * u) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hB _
  have hC' : 0 < (4 * Real.pi * (e + u)) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hC _
  field_simp

/-- **The semigroup splitting** in the frame coordinates, zeroth order. -/
theorem integral_anisoKernel_sub_mul_heatKernel {e : Fin d → ℝ} (he : ∀ k, 0 < e k) {u : ℝ}
    (hu : 0 < u) (w : Vec d) :
    ∫ y, anisoKernel e 0 (w - y) * euclideanHeatKernel u y = anisoKernel (fun k => e k + u) 0 w := by
  rw [euclideanHeatKernel_eq_prodFun hu]
  simp only [anisoKernel, prodFun]
  simp only [Pi.zero_apply, heatKernel1D_zero, Pi.sub_apply]
  simp_rw [← Finset.prod_mul_distrib]
  have h := integral_fintype_prod_volume_eq_prod (𝕜 := ℝ)
    (fun (k : Fin d) (y : ℝ) => heatKernel1 (e k) (w k - y) * heatKernel1 u y)
  rw [h]
  exact Finset.prod_congr rfl fun k _ => integral_heatKernel1_sub_mul (he k) hu (w k)

theorem integral_anisoKernel_sub_mul_heatKernel_succ {e : Fin d → ℝ} (he : ∀ k, 0 < e k) {u : ℝ}
    (hu : 0 < u) {n : Fin d → ℕ} (hn : ∀ k, n k ≤ 1)
    (hsplit : ∀ w, ∫ y, anisoKernel e n (w - y) * euclideanHeatKernel u y =
      anisoKernel (fun k => e k + u) n w) (j : Fin d) (w : Vec d) :
    ∫ y, anisoKernel e (n + Pi.single j 1) (w - y) * euclideanHeatKernel u y =
      anisoKernel (fun k => e k + u) (n + Pi.single j 1) w := by
  have heu : ∀ k, 0 < e k + u := fun k => add_pos (he k) hu
  have hK := contDiff_anisoKernel e n
  obtain ⟨C0, hC0⟩ := exists_abs_anisoKernel_le_const he n
  have hK1 : ∀ i, ∃ C, ∀ v, |coordinateDerivative i (anisoKernel e n) v| ≤ C := fun i => by
    obtain ⟨C, hC⟩ := exists_abs_anisoKernel_le_const he (n + Pi.single i 1)
    exact ⟨C, fun v => by rw [coordinateDerivative_anisoKernel he (hn i)]; exact hC v⟩
  have h := coordinateDerivative_integral_comp_sub hK ⟨C0, hC0⟩ hK1
    (integrable_euclideanHeatKernel hu) j w
  have hfun : (fun x => ∫ y, anisoKernel e n (x - y) * euclideanHeatKernel u y) =
      anisoKernel (fun k => e k + u) n := funext hsplit
  rw [hfun, coordinateDerivative_anisoKernel heu (hn j)] at h
  rw [h]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only
  rw [coordinateDerivative_anisoKernel he (hn j)]

/-- **The semigroup splitting** in the original coordinates:
`∫ Φ^{(n)}_e(Q x) Φ(u, v - x) dx = Φ^{(n)}_b(Q v)` whenever `Φ^{(n)}_e ∗ Φ_u = Φ^{(n)}_b`. -/
theorem integral_rotKernel_mul_heatKernel {Q : Mat d} (hQ : Q.transpose * Q = 1)
    {e b : Fin d → ℝ} {u : ℝ} {n : Fin d → ℕ}
    (hsplit : ∀ w, ∫ y, anisoKernel e n (w - y) * euclideanHeatKernel u y = anisoKernel b n w)
    (v : Vec d) :
    ∫ x, anisoKernel e n (Q *ᵥ x) * euclideanHeatKernel u (v - x) = anisoKernel b n (Q *ᵥ v) := by
  have h1 : ∀ x, anisoKernel e n (Q *ᵥ x) * euclideanHeatKernel u (v - x) =
      (fun x' => anisoKernel e n x' * euclideanHeatKernel u (Q *ᵥ v - x')) (Q *ᵥ x) := by
    intro x
    simp only
    rw [← Matrix.mulVec_sub, euclideanHeatKernel_mulVec_of_orthogonal hQ]
  simp_rw [h1]
  have h2 := integral_comp_mulVec_of_orthogonal hQ
    (fun x' => anisoKernel e n x' * euclideanHeatKernel u (Q *ᵥ v - x'))
  rw [h2, ← hsplit (Q *ᵥ v), ← integral_sub_left_eq_self _ volume (Q *ᵥ v)]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [sub_sub_cancel]

/-! ## The Hessian and the gradient of the products -/

theorem prod_heatPoly_single_add_single (t w : Vec d) (k m : Fin d) :
    ∏ j, heatPoly ((Pi.single k 1 + Pi.single m 1 : Fin d → ℕ) j) (t j) (w j) =
      w k * w m / (4 * t k * t m) - if k = m then 1 / (2 * t m) else 0 := by
  classical
  by_cases hkm : k = m
  · subst hkm
    have hpt : ∀ j, heatPoly ((Pi.single k 1 + Pi.single k 1 : Fin d → ℕ) j) (t j) (w j) =
        if j = k then heatFactor (t k) (w k) else 1 := by
      intro j
      by_cases hj : j = k
      · subst hj
        simp [heatPoly]
      · simp [hj, heatPoly]
    simp only [hpt, Finset.prod_ite_eq', Finset.mem_univ, ite_true, heatFactor]
    ring
  · have hpt : ∀ j, heatPoly ((Pi.single k 1 + Pi.single m 1 : Fin d → ℕ) j) (t j) (w j) =
        (if j = k then -(w k / (2 * t k)) else 1) * (if j = m then -(w m / (2 * t m)) else 1) := by
      intro j
      by_cases hj : j = k
      · subst hj
        simp [hkm, heatPoly]
      · by_cases hjm : j = m
        · subst hjm
          simp [hj, heatPoly]
        · simp [hj, hjm, heatPoly]
    simp only [hpt, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, ite_true,
      hkm, ite_false, sub_zero]
    ring

theorem prod_heatPoly_single (t w : Vec d) (k : Fin d) :
    ∏ j, heatPoly ((Pi.single k 1 : Fin d → ℕ) j) (t j) (w j) = -(w k / (2 * t k)) := by
  classical
  have hpt : ∀ j, heatPoly ((Pi.single k 1 : Fin d → ℕ) j) (t j) (w j) =
      if j = k then -(w k / (2 * t k)) else 1 := by
    intro j
    by_cases hj : j = k
    · subst hj
      simp [heatPoly]
    · simp [hj, heatPoly]
  simp only [hpt, Finset.prod_ite_eq', Finset.mem_univ, ite_true]

/-- `|(s_k v_k)_k| ≤ S |v|` when `|s_k| ≤ S`. -/
theorem euclideanNorm_mul_le {s v : Vec d} {S : ℝ} (hS : 0 ≤ S) (hs : ∀ k, |s k| ≤ S) :
    euclideanNorm (fun k => s k * v k) ≤ S * euclideanNorm v := by
  unfold euclideanNorm
  rw [← Real.sqrt_sq hS, ← Real.sqrt_mul (sq_nonneg S)]
  refine Real.sqrt_le_sqrt ?_
  unfold euclideanSq dot
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  have h1 : s k * s k ≤ S ^ 2 := by
    have := abs_mul_abs_self (s k)
    nlinarith [abs_nonneg (s k), hs k]
  nlinarith [mul_self_nonneg (v k)]

theorem anisoKernel_single_add_single (e w : Vec d) (k m : Fin d) :
    anisoKernel e (Pi.single k 1 + Pi.single m 1) w =
      (w k * w m / (4 * e k * e m) - if k = m then 1 / (2 * e m) else 0) * anisoKernel e 0 w := by
  rw [anisoKernel_eq_mul, prod_heatPoly_single_add_single]

theorem anisoKernel_single (e w : Vec d) (k : Fin d) :
    anisoKernel e (Pi.single k 1) w = -(w k / (2 * e k)) * anisoKernel e 0 w := by
  rw [anisoKernel_eq_mul, prod_heatPoly_single]

/-- The Hessian of the products contracted with two vectors. -/
theorem sum_hessian_anisoKernel_eq (e a c w : Vec d) :
    ∑ k, ∑ m, a k * c m * anisoKernel e (Pi.single k 1 + Pi.single m 1) w =
      anisoKernel e 0 w * (dot a (fun k => (2 * e k)⁻¹ * w k) *
        dot c (fun m => (2 * e m)⁻¹ * w m) - dot a (fun m => (2 * e m)⁻¹ * c m)) := by
  classical
  set G := anisoKernel e 0 w with hG
  have hterm : ∀ k m, a k * c m * anisoKernel e (Pi.single k 1 + Pi.single m 1) w =
      G * ((a k * ((2 * e k)⁻¹ * w k)) * (c m * ((2 * e m)⁻¹ * w m))) -
        G * (if k = m then a m * ((2 * e m)⁻¹ * c m) else 0) := by
    intro k m
    rw [anisoKernel_single_add_single, ← hG]
    split_ifs with h
    · subst h
      ring
    · ring
  rw [Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun m _ => hterm k m]
  have h1 : ∀ k, ∑ m, (G * ((a k * ((2 * e k)⁻¹ * w k)) * (c m * ((2 * e m)⁻¹ * w m))) -
      G * (if k = m then a m * ((2 * e m)⁻¹ * c m) else 0)) =
      G * (a k * ((2 * e k)⁻¹ * w k)) * ∑ m, c m * ((2 * e m)⁻¹ * w m) -
        G * (a k * ((2 * e k)⁻¹ * c k)) := by
    intro k
    have e1 : ∑ m, G * (if k = m then a m * ((2 * e m)⁻¹ * c m) else 0) =
        G * (a k * ((2 * e k)⁻¹ * c k)) := by
      rw [← Finset.mul_sum, Finset.sum_ite_eq]
      simp
    rw [Finset.sum_sub_distrib, e1, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun m _ => by ring
  rw [Finset.sum_congr rfl fun k _ => h1 k, Finset.sum_sub_distrib, ← Finset.sum_mul,
    ← Finset.mul_sum, ← Finset.mul_sum]
  simp only [dot]
  ring

theorem euclideanNorm_sq_eq (w : Vec d) : euclideanNorm w ^ 2 = euclideanSq w := by
  unfold euclideanNorm
  exact Real.sq_sqrt (BaseExponent.euclideanSq_nonneg w)

/-- **The Hessian bound**: for `u ≤ e_k ≤ K u`,
`|∑_{k,m} a_k c_m ∂_k ∂_m Φ_e(w)| ≤ (2K + 1/2) u⁻¹ (4πu)^{-d/2} e^{-|w|²/(8Ku)} |a| |c|`. -/
theorem abs_hessian_anisoKernel_le {K u : ℝ} (hu : 0 < u) (hK : 1 ≤ K) {e : Fin d → ℝ}
    (he : ∀ k, u ≤ e k ∧ e k ≤ K * u) (a c w : Vec d) :
    |∑ k, ∑ m, a k * c m * anisoKernel e (Pi.single k 1 + Pi.single m 1) w| ≤
      (2 * K + 1 / 2) * u⁻¹ * ((4 * Real.pi * u) ^ (-(d : ℝ) / 2) *
        Real.exp (-euclideanSq w / (8 * K * u))) * (euclideanNorm a * euclideanNorm c) := by
  have hK0 : 0 < K := lt_of_lt_of_le one_pos hK
  have he0 : ∀ k, 0 < e k := fun k => hu.trans_le (he k).1
  have hs : ∀ k, |(2 * e k)⁻¹| ≤ (2 * u)⁻¹ := fun k => by
    rw [abs_of_pos (inv_pos.mpr (by linarith [he0 k]))]
    exact inv_anti₀ (by positivity) (by linarith [(he k).1])
  have hS : 0 ≤ (2 * u)⁻¹ := by positivity
  have hX := euclideanNorm_mul_le (v := w) hS hs
  have hY := euclideanNorm_mul_le (v := c) hS hs
  have ha := BaseExponent.euclideanNorm_nonneg a
  have hc := BaseExponent.euclideanNorm_nonneg c
  have hw := BaseExponent.euclideanNorm_nonneg w
  have hu' : u ≠ 0 := hu.ne'
  have hK' : K ≠ 0 := hK0.ne'
  set X := euclideanNorm (fun k => (2 * e k)⁻¹ * w k)
  set Y := euclideanNorm (fun k => (2 * e k)⁻¹ * c k)
  have hX0 : 0 ≤ X := BaseExponent.euclideanNorm_nonneg _
  have h1 := BaseExponent.abs_dot_le a (fun k => (2 * e k)⁻¹ * w k)
  have h2 := BaseExponent.abs_dot_le c (fun k => (2 * e k)⁻¹ * w k)
  have h3 := BaseExponent.abs_dot_le a (fun k => (2 * e k)⁻¹ * c k)
  have hG0 := anisoKernel_zero_pos he0 w
  have hG := anisoKernel_zero_le hu he w
  set G := anisoKernel e 0 w
  rw [sum_hessian_anisoKernel_eq, abs_mul, abs_of_pos hG0]
  have hbr : |dot a (fun k => (2 * e k)⁻¹ * w k) * dot c (fun m => (2 * e m)⁻¹ * w m) -
      dot a (fun m => (2 * e m)⁻¹ * c m)| ≤
      euclideanNorm a * euclideanNorm c * ((2 * u)⁻¹ ^ 2 * euclideanNorm w ^ 2 + (2 * u)⁻¹) := by
    refine (abs_sub _ _).trans ?_
    rw [abs_mul]
    have e1 : |dot a (fun k => (2 * e k)⁻¹ * w k)| ≤ euclideanNorm a * ((2 * u)⁻¹ * euclideanNorm w) :=
      h1.trans (mul_le_mul_of_nonneg_left hX ha)
    have e2 : |dot c (fun k => (2 * e k)⁻¹ * w k)| ≤ euclideanNorm c * ((2 * u)⁻¹ * euclideanNorm w) :=
      h2.trans (mul_le_mul_of_nonneg_left hX hc)
    have e3 : |dot a (fun k => (2 * e k)⁻¹ * c k)| ≤ euclideanNorm a * ((2 * u)⁻¹ * euclideanNorm c) :=
      h3.trans (mul_le_mul_of_nonneg_left hY ha)
    calc |dot a (fun k => (2 * e k)⁻¹ * w k)| * |dot c (fun m => (2 * e m)⁻¹ * w m)| +
          |dot a (fun m => (2 * e m)⁻¹ * c m)|
        ≤ (euclideanNorm a * ((2 * u)⁻¹ * euclideanNorm w)) *
            (euclideanNorm c * ((2 * u)⁻¹ * euclideanNorm w)) +
          euclideanNorm a * ((2 * u)⁻¹ * euclideanNorm c) :=
          add_le_add (mul_le_mul e1 e2 (abs_nonneg _) (by positivity)) e3
      _ = _ := by ring
  set s := euclideanSq w / (8 * K * u) with hsdef
  have hs0 : 0 ≤ s := div_nonneg (BaseExponent.euclideanSq_nonneg w) (by positivity)
  have hE2 : Real.exp (-euclideanSq w / (4 * (K * u))) = Real.exp (-s) * Real.exp (-s) := by
    rw [← Real.exp_add, hsdef]
    congr 1
    field_simp
    ring
  have hw2 : euclideanNorm w ^ 2 = 8 * K * u * s := by
    rw [euclideanNorm_sq_eq, hsdef]
    field_simp
  have hsE := mul_exp_neg_le_one s
  have hE1 : Real.exp (-s) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hE0 := Real.exp_pos (-s)
  set P := (4 * Real.pi * u) ^ (-(d : ℝ) / 2) with hP
  have hP0 : 0 ≤ P := by positivity
  rw [show -euclideanSq w / (8 * K * u) = -s by rw [hsdef]; ring]
  calc G * |dot a (fun k => (2 * e k)⁻¹ * w k) * dot c (fun m => (2 * e m)⁻¹ * w m) -
        dot a (fun m => (2 * e m)⁻¹ * c m)|
      ≤ (P * (Real.exp (-s) * Real.exp (-s))) *
          (euclideanNorm a * euclideanNorm c * ((2 * u)⁻¹ ^ 2 * euclideanNorm w ^ 2 + (2 * u)⁻¹)) := by
        rw [← hE2]
        exact mul_le_mul hG hbr (abs_nonneg _) (by positivity)
    _ = P * Real.exp (-s) * (euclideanNorm a * euclideanNorm c) * u⁻¹ *
          (2 * K * (s * Real.exp (-s)) + Real.exp (-s) / 2) := by
        rw [hw2]
        field_simp
        ring
    _ ≤ P * Real.exp (-s) * (euclideanNorm a * euclideanNorm c) * u⁻¹ * (2 * K * 1 + 1 / 2) := by
        gcongr
    _ = _ := by ring

/-- **The gradient bound**: for `β₁ ≤ b_k ≤ β₂`,
`|∑_k a_k ∂_k Φ_b(w)| ≤ (4πβ₁)^{-d/2} (√(8β₂)/(2β₁)) e^{-|w|²/(8β₂)} |a|`. -/
theorem abs_gradient_anisoKernel_le {β₁ β₂ : ℝ} (hβ₁ : 0 < β₁) (hβ : β₁ ≤ β₂) {b : Fin d → ℝ}
    (hb : ∀ k, β₁ ≤ b k ∧ b k ≤ β₂) (a w : Vec d) :
    |∑ k, a k * anisoKernel b (Pi.single k 1) w| ≤
      (4 * Real.pi * β₁) ^ (-(d : ℝ) / 2) * (Real.sqrt (8 * β₂) / (2 * β₁)) *
        Real.exp (-euclideanSq w / (8 * β₂)) * euclideanNorm a := by
  have hβ₂ : 0 < β₂ := hβ₁.trans_le hβ
  have hb0 : ∀ k, 0 < b k := fun k => hβ₁.trans_le (hb k).1
  have hsum : ∑ k, a k * anisoKernel b (Pi.single k 1) w =
      -(anisoKernel b 0 w * dot a (fun k => (2 * b k)⁻¹ * w k)) := by
    simp only [anisoKernel_single, dot, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have hs : ∀ k, |(2 * b k)⁻¹| ≤ (2 * β₁)⁻¹ := fun k => by
    rw [abs_of_pos (inv_pos.mpr (by linarith [hb0 k]))]
    exact inv_anti₀ (by positivity) (by linarith [(hb k).1])
  have hX := euclideanNorm_mul_le (v := w) (by positivity : (0 : ℝ) ≤ (2 * β₁)⁻¹) hs
  have h1 := BaseExponent.abs_dot_le a (fun k => (2 * b k)⁻¹ * w k)
  have hG0 := anisoKernel_zero_pos hb0 w
  have hG := anisoKernel_zero_le hβ₁ hb w
  have ha := BaseExponent.euclideanNorm_nonneg a
  rw [hsum, abs_neg, abs_mul, abs_of_pos hG0]
  set E := Real.exp (-euclideanSq w / (8 * β₂)) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hE2 : Real.exp (-euclideanSq w / (4 * β₂)) = E * E := by
    rw [hE, ← Real.exp_add]
    congr 1
    field_simp
    ring
  have hwE : euclideanNorm w * E ≤ Real.sqrt (8 * β₂) := by
    have hq : 0 < Real.sqrt (8 * β₂) := Real.sqrt_pos.mpr (by positivity)
    set τ := euclideanNorm w / Real.sqrt (8 * β₂) with hτ
    have hτ0 : 0 ≤ τ := div_nonneg (BaseExponent.euclideanNorm_nonneg w) hq.le
    have hτ2 : τ ^ 2 = euclideanSq w / (8 * β₂) := by
      rw [hτ, div_pow, euclideanNorm_sq_eq, Real.sq_sqrt (by positivity)]
    have hτle : τ ≤ Real.exp (τ ^ 2) := by
      have := Real.add_one_le_exp (τ ^ 2)
      nlinarith [sq_nonneg (τ - 1 / 2)]
    have hEτ : E = Real.exp (-(τ ^ 2)) := by rw [hE, hτ2, neg_div]
    have hw : euclideanNorm w = Real.sqrt (8 * β₂) * τ := by
      rw [hτ]
      field_simp
    have hτE : τ * Real.exp (-(τ ^ 2)) ≤ 1 := by
      calc τ * Real.exp (-(τ ^ 2)) ≤ Real.exp (τ ^ 2) * Real.exp (-(τ ^ 2)) :=
            mul_le_mul_of_nonneg_right hτle (Real.exp_pos _).le
        _ = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    rw [hw, hEτ, mul_assoc]
    calc Real.sqrt (8 * β₂) * (τ * Real.exp (-(τ ^ 2))) ≤ Real.sqrt (8 * β₂) * 1 :=
          mul_le_mul_of_nonneg_left hτE hq.le
      _ = Real.sqrt (8 * β₂) := mul_one _
  set P := (4 * Real.pi * β₁) ^ (-(d : ℝ) / 2) with hP
  have hP0 : 0 ≤ P := by positivity
  calc anisoKernel b 0 w * |dot a (fun k => (2 * b k)⁻¹ * w k)|
      ≤ (P * (E * E)) * (euclideanNorm a * ((2 * β₁)⁻¹ * euclideanNorm w)) := by
        rw [← hE2]
        exact mul_le_mul hG (h1.trans (mul_le_mul_of_nonneg_left hX ha)) (abs_nonneg _)
          (by positivity)
    _ = P * (2 * β₁)⁻¹ * E * euclideanNorm a * (euclideanNorm w * E) := by ring
    _ ≤ P * (2 * β₁)⁻¹ * E * euclideanNorm a * Real.sqrt (8 * β₂) := by gcongr
    _ = _ := by ring

end QSH
