import QuantitativeStochasticHomogenization.Ch04.Sec04.SmoothedCorrectorPathwise
import QuantitativeStochasticHomogenization.Ch04.Sec04.PolynomialGrowth

/-!
# The scales of the smoothed observation

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
proof of Lemma 4.21 (SCOTT-localization (5)), the exponents. With `S = r^{a₁}`, `ρ = σ S`,
`R = S r^{ε'}`, `T = r^{1+δ}` and `ε'(d + 1) ≤ κ a₁/2`, the main term of the Gaussian gradient
averages decays like `r^{ε'(d+1-κ) - κ a₁} ≤ r^{-κ a₁/2}`, and the Gaussian error terms, which are
polynomials in `r` times `e^{-r^{2ε'}/(128σ²)}`, are eventually below `r^{-μ}` and `S^{-β}`.
-/

open MeasureTheory Filter Topology

noncomputable section

namespace QSH

variable {d : ℕ}

theorem rpow_mul_rpow_sq {r a : ℝ} (hr : 0 ≤ r) : (r ^ a) ^ 2 = r ^ (2 * a) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hr]
  congr 1
  push_cast
  ring

/-- The exponent of the Gaussian factors at the scales `R = S r^{ε'}`, `ρ = σ S`. -/
theorem gaussExponent_eq {S r σ ε' : ℝ} (hS : 0 < S) (hσ : 0 < σ) (hr : 0 ≤ r) (k : ℝ)
    (hk : 0 < k) :
    -((S * r ^ ε' / 2) ^ 2) / (k * (σ * S) ^ 2) = -(1 / (4 * k * σ ^ 2) * r ^ (2 * ε')) := by
  rw [← rpow_mul_rpow_sq hr]
  have := hS.ne'; have := hσ.ne'; have := hk.ne'
  field_simp
  ring

theorem gaussTail'_eq {S r σ ε' : ℝ} (hS : 0 < S) (hσ : 0 < σ) (hr : 0 ≤ r) :
    gaussTail' d (S * r ^ ε') (σ * S) =
      (2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp (-(1 / (128 * σ ^ 2) * r ^ (2 * ε'))) := by
  unfold gaussTail'
  rw [gaussExponent_eq hS hσ hr 32 (by norm_num)]
  norm_num

theorem gaussTail_le {S r σ ε' : ℝ} (hS : 0 < S) (hσ : 0 < σ) (hr : 0 ≤ r) :
    gaussTail d (S * r ^ ε') (σ * S) ≤
      heatKernelPeak d (σ * S) * Real.exp (-(1 / (128 * σ ^ 2) * r ^ (2 * ε'))) := by
  unfold gaussTail
  rw [gaussExponent_eq hS hσ hr 16 (by norm_num)]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_)
    (heatKernelPeak_pos (mul_pos hσ hS).ne').le
  have : 0 ≤ r ^ (2 * ε') := Real.rpow_nonneg hr _
  have hσ2 := pow_pos hσ 2
  have h1 : 1 / (128 * σ ^ 2) ≤ 1 / (4 * 16 * σ ^ 2) :=
    one_div_le_one_div_of_le (by linarith) (by linarith)
  nlinarith

theorem heatKernelPeak_le_of_le {ρ₀ ρ : ℝ} (hρ₀ : 0 < ρ₀) (hρ : ρ₀ ≤ ρ) :
    heatKernelPeak d ρ ≤ heatKernelPeak d ρ₀ := by
  unfold heatKernelPeak
  apply Real.rpow_le_rpow_of_nonpos (mul_pos (mul_pos four_pos Real.pi_pos) (pow_pos hρ₀ 2))
  · have := pow_le_pow_left₀ hρ₀.le hρ 2
    nlinarith [Real.pi_pos]
  · have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith

theorem heatKernelPeak_mul_rpow {σ a r : ℝ} (hσ : 0 < σ) (hr : 0 < r) :
    heatKernelPeak d (σ * r ^ a) =
      (4 * Real.pi * σ ^ 2) ^ (-(d : ℝ) / 2) * r ^ (-(a * d)) := by
  unfold heatKernelPeak
  have e : 4 * Real.pi * (σ * r ^ a) ^ 2 = (4 * Real.pi * σ ^ 2) * r ^ (2 * a) := by
    rw [mul_pow, rpow_mul_rpow_sq hr.le]; ring
  rw [e, Real.mul_rpow (by positivity) (Real.rpow_nonneg hr.le _), ← Real.rpow_mul hr.le]
  congr 2
  ring

theorem rpow_natCast_pow {r a : ℝ} (hr : 0 ≤ r) (n : ℕ) : (r ^ a) ^ n = r ^ (a * n) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hr]

theorem two_mul_rpow_pow {r a b : ℝ} (hr : 0 ≤ r) :
    (2 * r ^ a) ^ b = 2 ^ b * r ^ (a * b) := by
  rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hr a), ← Real.rpow_mul hr]

/-- **The oscillation bound at the radius `r^a`** has polynomial growth. -/
theorem polyGrowth_correctorOscillation (C₈ κ a : ℝ) :
    PolyGrowth fun r => correctorOscillation d C₈ κ (r ^ a) := by
  unfold correctorOscillation
  have h1 : PolyGrowth fun r : ℝ => (2 * r ^ a) ^ (1 - κ) :=
    (powerBound_const_mul_rpow (2 ^ (1 - κ)) (a * (1 - κ))).polyGrowth.of_le fun r hr => by
      rw [two_mul_rpow_pow (zero_le_one.trans hr)]
  have h2 : PolyGrowth fun r : ℝ => (r ^ a) ^ d := (polyGrowth_rpow a).pow d
  exact ((polyGrowth_const _).mul ((h1.const_mul C₈).pow 2)).mul
    (h2.mul (polyGrowth_const _))

theorem exp_ratio_eq {S θ σ : ℝ} (hS : 0 < S) (hθ : 0 < θ) (hσ : 0 < σ) :
    (S / θ) ^ 2 / (4 * (Real.sqrt 2 * (σ * S)) ^ 2) = 1 / (8 * θ ^ 2 * σ ^ 2) := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have := hS.ne'; have := hθ.ne'; have := hσ.ne'
  rw [mul_pow, mul_pow, h2]
  field_simp
  try ring

/-- The Gaussian energy bound `Eg` at the radius `r` (`t₀ = r + d`). -/
def obsEnergy (d : ℕ) (C₈ σ θ r : ℝ) : ℝ :=
  (2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp (1 / (8 * θ ^ 2 * σ ^ 2)) *
    (gaussianBallConstant d * (correctorEnergyDensity d C₈ * volume.real (ball (0 : Vec d) 1)) *
      (r + d) ^ d)

/-- The oscillation bound `W` around the cut-off mean on `B_T`, `T = r^{1+δ}`. -/
def obsOscillation (d : ℕ) (C₈ κ σ a₁ δ r : ℝ) : ℝ :=
  2 * correctorOscillation d C₈ κ (r ^ (1 + δ)) + 8 * heatKernelPeak d (σ * r ^ a₁) ^ 2 *
    ((r ^ (1 + δ)) ^ d * volume.real (ball (0 : Vec d) 1)) ^ 2 *
      correctorOscillation d C₈ κ (r ^ (1 + δ))

/-- The error term `E` of the smoothed observation at the radius `r`. -/
def obsError (d : ℕ) (C₈ κ D σ θ a₁ ε' δ r : ℝ) : ℝ :=
  (r ^ a₁ / θ) * (d * (gaussTail' d (r ^ a₁ * r ^ ε') (σ * r ^ a₁) * Real.sqrt (obsEnergy d C₈ σ θ r) +
    D / (r ^ a₁ * r ^ ε') * gaussTail d (r ^ a₁ * r ^ ε') (σ * r ^ a₁) *
      Real.sqrt ((r ^ a₁ * r ^ ε') ^ d * volume.real (ball (0 : Vec d) 1) *
        obsOscillation d C₈ κ σ a₁ δ r))) +
    gaussTail d (r ^ a₁ * r ^ ε') (σ * r ^ a₁) *
      Real.sqrt ((r ^ (1 + δ)) ^ d * volume.real (ball (0 : Vec d) 1) *
        obsOscillation d C₈ κ σ a₁ δ r)

/-- The bound `G` of the Gaussian gradient averages at the radius `r`. -/
def obsGradient (d : ℕ) (C₈ κ D σ θ a₁ ε' r : ℝ) : ℝ :=
  Real.sqrt d * (((2 : ℝ) ^ ((d : ℝ) / 2) * (2 / (σ * r ^ a₁)) *
      (4 * Real.pi * (2 * (σ * r ^ a₁) ^ 2)) ^ (-(d : ℝ) / 2) +
      D / (r ^ a₁ * r ^ ε') * heatKernelPeak d (σ * r ^ a₁)) *
    Real.sqrt ((r ^ a₁ * r ^ ε') ^ d * volume.real (ball (0 : Vec d) 1) *
      correctorOscillation d C₈ κ (r ^ a₁ * r ^ ε')) +
    gaussTail' d (r ^ a₁ * r ^ ε') (σ * r ^ a₁) * Real.sqrt (obsEnergy d C₈ σ θ r))

theorem rpow_mul_rpow_eq {r a b : ℝ} (hr : 0 < r) : r ^ a * r ^ b = r ^ (a + b) :=
  (Real.rpow_add hr a b).symm

/-- **The main term of the Gaussian gradient averages** decays like `r^{ε'(d+1) - κ(a₁+ε')}`. -/
theorem powerBound_obsGradient_main (d : ℕ) (C₈ κ D σ a₁ ε' : ℝ) (hσ : 0 < σ) (hD : 0 ≤ D)
    (hε' : 0 ≤ ε') :
    PowerBound (fun r => ((2 : ℝ) ^ ((d : ℝ) / 2) * (2 / (σ * r ^ a₁)) *
      (4 * Real.pi * (2 * (σ * r ^ a₁) ^ 2)) ^ (-(d : ℝ) / 2) +
      D / (r ^ a₁ * r ^ ε') * heatKernelPeak d (σ * r ^ a₁)) *
    Real.sqrt ((r ^ a₁ * r ^ ε') ^ d * volume.real (ball (0 : Vec d) 1) *
      correctorOscillation d C₈ κ (r ^ a₁ * r ^ ε')))
      (ε' * (d + 1) - κ * (a₁ + ε')) := by
  set b := a₁ + ε' with hb
  have hr0 : ∀ r : ℝ, 1 ≤ r → 0 < r := fun r hr => zero_lt_one.trans_le hr
  -- the factors of the cutoff derivative bound
  have p1 : PowerBound (fun r => (2 : ℝ) ^ ((d : ℝ) / 2) * (2 / (σ * r ^ a₁)) *
      (4 * Real.pi * (2 * (σ * r ^ a₁) ^ 2)) ^ (-(d : ℝ) / 2)) (-(a₁ * (d + 1))) := by
    refine (powerBound_const_mul_rpow ((2 : ℝ) ^ ((d : ℝ) / 2) * (2 / σ) *
      (8 * Real.pi * σ ^ 2) ^ (-(d : ℝ) / 2)) (-(a₁ * (d + 1)))).congr fun r hr => ?_
    have hr' := hr0 r hr
    have e1 : 4 * Real.pi * (2 * (σ * r ^ a₁) ^ 2) = (8 * Real.pi * σ ^ 2) * r ^ (2 * a₁) := by
      rw [mul_pow, rpow_mul_rpow_sq hr'.le]; ring
    rw [e1, Real.mul_rpow (by positivity) (Real.rpow_nonneg hr'.le _), ← Real.rpow_mul hr'.le]
    have e2 : 2 / (σ * r ^ a₁) = 2 / σ * r ^ (-a₁) := by
      rw [Real.rpow_neg hr'.le]; field_simp
    rw [e2]
    have e3 : r ^ (-(a₁ * (d + 1))) = r ^ (-a₁) * r ^ (2 * a₁ * (-(d : ℝ) / 2)) := by
      rw [← Real.rpow_add hr']; congr 1; ring
    rw [e3]
    ring
  have p2 : PowerBound (fun r => D / (r ^ a₁ * r ^ ε') * heatKernelPeak d (σ * r ^ a₁))
      (-(a₁ * (d + 1))) := by
    refine ((powerBound_const_mul_rpow (D * (4 * Real.pi * σ ^ 2) ^ (-(d : ℝ) / 2))
      (-(b + a₁ * d))).congr fun r hr => ?_).mono ?_
    · have hr' := hr0 r hr
      rw [heatKernelPeak_mul_rpow hσ hr', rpow_mul_rpow_eq hr', div_eq_mul_inv,
        ← Real.rpow_neg hr'.le]
      have e3 : r ^ (-(b + a₁ * d)) = r ^ (-(a₁ + ε')) * r ^ (-(a₁ * d)) := by
        rw [← Real.rpow_add hr']; congr 1; rw [hb]; ring
      rw [e3]
      ring
    · rw [hb]; nlinarith
  -- the oscillation factor
  have pR : PowerBound (fun r => r ^ a₁ * r ^ ε') b :=
    (powerBound_const_mul_rpow 1 b).congr fun r hr => by
      rw [rpow_mul_rpow_eq (hr0 r hr), one_mul]
  have p2R : PowerBound (fun r => (2 * (r ^ a₁ * r ^ ε')) ^ (1 - κ)) (b * (1 - κ)) :=
    (powerBound_const_mul_rpow ((2 : ℝ) ^ (1 - κ)) (b * (1 - κ))).congr fun r hr => by
      rw [rpow_mul_rpow_eq (hr0 r hr), two_mul_rpow_pow (hr0 r hr).le]
  have pV := ((powerBound_const ((2 : ℝ) ^ d)).mul (((powerBound_const C₈).mul p2R).pow 2)).mul
    ((pR.pow d).mul (powerBound_const (volume.real (ball (0 : Vec d) 1))))
  have pin := ((pR.pow d).mul (powerBound_const (volume.real (ball (0 : Vec d) 1)))).mul pV
  have psq := pin.sqrt
  refine ((p1.add p2).mul psq).mono (le_of_eq ?_)
  rw [hb]
  push_cast
  ring

theorem obsError_le (d : ℕ) {C₈ κ D σ θ a₁ ε' δ r : ℝ} (hσ : 0 < σ) (hθ : 0 < θ) (hD : 0 ≤ D)
    (hr : 1 ≤ r) (ha₁ : 0 ≤ a₁) (hε' : 0 ≤ ε') :
    obsError d C₈ κ D σ θ a₁ ε' δ r ≤
      Real.exp (-(1 / (128 * σ ^ 2) * r ^ (2 * ε'))) *
        ((r ^ a₁ / θ) * (d * ((2 : ℝ) ^ ((d : ℝ) / 2) * Real.sqrt (obsEnergy d C₈ σ θ r) +
          D * heatKernelPeak d σ * Real.sqrt ((r ^ a₁ * r ^ ε') ^ d *
            volume.real (ball (0 : Vec d) 1) * obsOscillation d C₈ κ σ a₁ δ r))) +
          heatKernelPeak d σ * Real.sqrt ((r ^ (1 + δ)) ^ d * volume.real (ball (0 : Vec d) 1) *
            obsOscillation d C₈ κ σ a₁ δ r)) := by
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hS : 0 < r ^ a₁ := Real.rpow_pos_of_pos hr0 _
  have hS1 : 1 ≤ r ^ a₁ := Real.one_le_rpow hr ha₁
  have hR1 : 1 ≤ r ^ a₁ * r ^ ε' := one_le_mul_of_one_le_of_one_le hS1 (Real.one_le_rpow hr hε')
  set e := Real.exp (-(1 / (128 * σ ^ 2) * r ^ (2 * ε'))) with he
  have he0 : 0 ≤ e := (Real.exp_pos _).le
  have hpk : heatKernelPeak d (σ * r ^ a₁) ≤ heatKernelPeak d σ :=
    heatKernelPeak_le_of_le hσ (le_mul_of_one_le_right hσ.le hS1)
  have h1 : gaussTail' d (r ^ a₁ * r ^ ε') (σ * r ^ a₁) = (2 : ℝ) ^ ((d : ℝ) / 2) * e :=
    gaussTail'_eq hS hσ hr0.le
  have h2 : gaussTail d (r ^ a₁ * r ^ ε') (σ * r ^ a₁) ≤ heatKernelPeak d σ * e :=
    (gaussTail_le hS hσ hr0.le).trans (mul_le_mul_of_nonneg_right hpk he0)
  have h3 : D / (r ^ a₁ * r ^ ε') ≤ D := div_le_self hD hR1
  have hg0 := gaussTail_nonneg d (r ^ a₁ * r ^ ε') (mul_pos hσ hS)
  set X₁ := Real.sqrt ((r ^ a₁ * r ^ ε') ^ d * volume.real (ball (0 : Vec d) 1) *
    obsOscillation d C₈ κ σ a₁ δ r) with hX₁
  set X₂ := Real.sqrt ((r ^ (1 + δ)) ^ d * volume.real (ball (0 : Vec d) 1) *
    obsOscillation d C₈ κ σ a₁ δ r) with hX₂
  set E₀ := Real.sqrt (obsEnergy d C₈ σ θ r) with hE₀
  have hX₁0 : 0 ≤ X₁ := Real.sqrt_nonneg _
  have hX₂0 : 0 ≤ X₂ := Real.sqrt_nonneg _
  have hE₀0 : 0 ≤ E₀ := Real.sqrt_nonneg _
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hSθ : 0 ≤ r ^ a₁ / θ := (div_pos hS hθ).le
  unfold obsError
  rw [← hX₁, ← hX₂, ← hE₀, h1]
  have k1 : D / (r ^ a₁ * r ^ ε') * gaussTail d (r ^ a₁ * r ^ ε') (σ * r ^ a₁) * X₁ ≤
      D * (heatKernelPeak d σ * e) * X₁ :=
    mul_le_mul_of_nonneg_right (mul_le_mul h3 h2 hg0 hD) hX₁0
  have k2 : gaussTail d (r ^ a₁ * r ^ ε') (σ * r ^ a₁) * X₂ ≤ heatKernelPeak d σ * e * X₂ :=
    mul_le_mul_of_nonneg_right h2 hX₂0
  have k3 : r ^ a₁ / θ * (d * (2 ^ ((d : ℝ) / 2) * e * E₀ +
      D / (r ^ a₁ * r ^ ε') * gaussTail d (r ^ a₁ * r ^ ε') (σ * r ^ a₁) * X₁)) ≤
      r ^ a₁ / θ * (d * (2 ^ ((d : ℝ) / 2) * e * E₀ + D * (heatKernelPeak d σ * e) * X₁)) := by
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hd0) hSθ
    linarith
  calc _ ≤ r ^ a₁ / θ * (d * (2 ^ ((d : ℝ) / 2) * e * E₀ + D * (heatKernelPeak d σ * e) * X₁)) +
        heatKernelPeak d σ * e * X₂ := add_le_add k3 k2
    _ = _ := by ring

theorem polyGrowth_obsEnergy (d : ℕ) (C₈ σ θ : ℝ) : PolyGrowth (obsEnergy d C₈ σ θ) := by
  unfold obsEnergy
  exact (polyGrowth_const _).mul ((polyGrowth_const _).mul
    ((polyGrowth_id.add (polyGrowth_const (d : ℝ))).pow d))

theorem polyGrowth_obsOscillation (d : ℕ) (C₈ κ σ a₁ δ : ℝ) (hσ : 0 < σ) (ha₁ : 0 ≤ a₁) :
    PolyGrowth (obsOscillation d C₈ κ σ a₁ δ) := by
  unfold obsOscillation
  have hV := polyGrowth_correctorOscillation (d := d) C₈ κ (1 + δ)
  have hpk : PolyGrowth fun r => heatKernelPeak d (σ * r ^ a₁) ^ 2 :=
    ((polyGrowth_const (heatKernelPeak d σ)).pow 2).of_le fun r hr => by
      have h1 : 1 ≤ r ^ a₁ := Real.one_le_rpow hr ha₁
      have h2 := heatKernelPeak_le_of_le (d := d) hσ (le_mul_of_one_le_right hσ.le h1)
      have h3 := (heatKernelPeak_pos (d := d) (mul_pos hσ (zero_lt_one.trans_le h1)).ne').le
      rw [abs_of_nonneg (sq_nonneg _), abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ h3 h2 2
  have hT := (((polyGrowth_rpow (1 + δ)).pow d).mul (polyGrowth_const
    (volume.real (ball (0 : Vec d) 1)))).pow 2
  exact (hV.const_mul 2).add (((hpk.const_mul 8).mul hT).mul hV)

/-- **The scales of the smoothed observation**: for `r ≥ r₀` the radii are ordered, the cut-off
mass is at least `1/2`, the Gaussian gradient bound decays like `r^{-κa₁/2}` and the error term is
below `r^{-κa₁/2}` and `S^{-β}`. -/
theorem smoothed_scales (d : ℕ) {C₈ κ D σ θ a₁ ε' δ β : ℝ} (hσ : 0 < σ) (hθ : 0 < θ)
    (ha₁ : 1 < a₁) (hε' : 0 < ε') (hκ : 0 < κ) (hD : 0 ≤ D)
    (hε'κ : ε' * (d + 1) ≤ κ * a₁ / 2) :
    ∃ r₀ K : ℝ, 2 ≤ r₀ ∧ 0 ≤ K ∧ ∀ r : ℝ, r₀ ≤ r →
      4 * (r ^ a₁ / θ) ≤ r ^ a₁ * r ^ ε' ∧ 1 ≤ σ * r ^ a₁ ∧ r + d ≤ r ^ a₁ * r ^ ε' ∧
      (2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp (-((r ^ a₁ * r ^ ε' / 2) ^ 2) / (8 * (σ * r ^ a₁) ^ 2))
        ≤ 1 / 2 ∧
      obsGradient d C₈ κ D σ θ a₁ ε' r ≤ K * r ^ (-(κ * a₁ / 2)) ∧
      Real.sqrt 2 * obsError d C₈ κ D σ θ a₁ ε' δ r / r ^ a₁ ≤ r ^ (-(κ * a₁ / 2)) ∧
      Real.sqrt 2 * obsError d C₈ κ D σ θ a₁ ε' δ r / r ^ a₁ ≤ (r ^ a₁) ^ (-β) := by
  set μ := κ * a₁ / 2 with hμ
  set c := 1 / (128 * σ ^ 2) with hc
  have hc0 : 0 < c := one_div_pos.2 (mul_pos (by norm_num) (pow_pos hσ 2))
  have hb : 0 < 2 * ε' := mul_pos two_pos hε'
  have ha₁0 : 0 ≤ a₁ := by linarith
  set Q : ℝ → ℝ := fun r => (r ^ a₁ / θ) * (d * ((2 : ℝ) ^ ((d : ℝ) / 2) *
      Real.sqrt (obsEnergy d C₈ σ θ r) + D * heatKernelPeak d σ * Real.sqrt ((r ^ a₁ * r ^ ε') ^ d *
        volume.real (ball (0 : Vec d) 1) * obsOscillation d C₈ κ σ a₁ δ r))) +
      heatKernelPeak d σ * Real.sqrt ((r ^ (1 + δ)) ^ d * volume.real (ball (0 : Vec d) 1) *
        obsOscillation d C₈ κ σ a₁ δ r) with hQ
  have hE := polyGrowth_obsEnergy d C₈ σ θ
  have hW := polyGrowth_obsOscillation d C₈ κ σ a₁ δ hσ ha₁0
  have hQg : PolyGrowth Q := by
    have hR := ((polyGrowth_rpow a₁).mul (polyGrowth_rpow ε')).pow d
    have hT := (polyGrowth_rpow (1 + δ)).pow d
    have h1 : PolyGrowth fun r : ℝ => r ^ a₁ / θ :=
      ((polyGrowth_rpow a₁).mul (polyGrowth_const θ⁻¹)).of_le fun r _ => by
        rw [div_eq_mul_inv]
    exact (h1.mul ((polyGrowth_const (d : ℝ)).mul (((polyGrowth_const _).mul hE.sqrt).add
      ((polyGrowth_const _).mul ((hR.mul (polyGrowth_const _)).mul hW).sqrt)))).add
      ((polyGrowth_const _).mul ((hT.mul (polyGrowth_const _)).mul hW).sqrt)
  have hdiv : PolyGrowth fun r : ℝ => r ^ (-a₁) := polyGrowth_rpow (-a₁)
  have hP1 : PolyGrowth fun r => Real.sqrt 2 * Q r * r ^ μ * r ^ (-a₁) :=
    (((polyGrowth_const _).mul hQg).mul (polyGrowth_rpow μ)).mul hdiv
  have hP2 : PolyGrowth fun r => Real.sqrt 2 * Q r * r ^ (a₁ * β) * r ^ (-a₁) :=
    (((polyGrowth_const _).mul hQg).mul (polyGrowth_rpow (a₁ * β))).mul hdiv
  have hP3 : PolyGrowth fun r => Real.sqrt d * (2 : ℝ) ^ ((d : ℝ) / 2) *
      Real.sqrt (obsEnergy d C₈ σ θ r) * r ^ μ :=
    ((polyGrowth_const _).mul hE.sqrt).mul (polyGrowth_rpow μ)
  have ev := (eventually_ge_atTop (2 : ℝ)).and ((eventually_le_rpow hε' (4 / θ)).and
    ((eventually_le_rpow (by linarith : 0 < a₁) (1 / σ)).and
    ((eventually_le_rpow (by linarith : 0 < a₁ - 1) (1 + d)).and
    (((polyGrowth_const ((2 : ℝ) ^ ((d : ℝ) / 2))).eventually_mul_exp_neg_le hb
      (one_div_pos.2 (mul_pos (by norm_num) (pow_pos hσ 2)) : (0 : ℝ) < 1 / (32 * σ ^ 2))
      (by norm_num : (0 : ℝ) < 1 / 2)).and
    ((hP1.eventually_mul_exp_neg_le hb hc0 one_pos).and
    ((hP2.eventually_mul_exp_neg_le hb hc0 one_pos).and
    (hP3.eventually_mul_exp_neg_le hb hc0 one_pos)))))))
  obtain ⟨r₀, hr₀⟩ := eventually_atTop.1 ev
  obtain ⟨K₁, hK₁, hmain⟩ := ((powerBound_obsGradient_main d C₈ κ D σ a₁ ε' hσ hD hε'.le).mono
    (show ε' * (d + 1) - κ * (a₁ + ε') ≤ -μ by nlinarith)).le
  refine ⟨max r₀ 2, Real.sqrt d * K₁ + 1, le_max_right _ _,
    add_nonneg (mul_nonneg (Real.sqrt_nonneg _) hK₁) zero_le_one, fun r hr => ?_⟩
  obtain ⟨h2, h4θ, h1σ, hd1, hsm, hT1, hT2, hT3⟩ := hr₀ r (le_of_max_le_left hr)
  have hr1 : 1 ≤ r := by linarith
  have hr0 : 0 < r := by linarith
  have hS : 0 < r ^ a₁ := Real.rpow_pos_of_pos hr0 _
  have hε1 : 1 ≤ r ^ ε' := Real.one_le_rpow hr1 hε'.le
  have hμr : 0 < r ^ μ := Real.rpow_pos_of_pos hr0 _
  have hEr := obsError_le d (C₈ := C₈) (κ := κ) (δ := δ) hσ hθ hD hr1 ha₁0 hε'.le
  set e := Real.exp (-(c * r ^ (2 * ε'))) with he
  have he0 : 0 ≤ e := (Real.exp_pos _).le
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : r ^ a₁ * (4 / θ) ≤ r ^ a₁ * r ^ ε' := mul_le_mul_of_nonneg_left h4θ hS.le
    calc 4 * (r ^ a₁ / θ) = r ^ a₁ * (4 / θ) := by ring
      _ ≤ _ := this
  · have := mul_le_mul_of_nonneg_left h1σ hσ.le
    rwa [mul_one_div_cancel hσ.ne'] at this
  · have e1 : r ^ a₁ = r * r ^ (a₁ - 1) := by
      rw [← Real.rpow_one_add' hr0.le (by linarith)]; congr 1; ring
    have : r + d ≤ r ^ a₁ := by
      rw [e1]; nlinarith [Nat.cast_nonneg (α := ℝ) d]
    nlinarith
  · rw [gaussExponent_eq hS hσ hr0.le 8 (by norm_num)]
    have e2 : 1 / (4 * 8 * σ ^ 2) = 1 / (32 * σ ^ 2) := by ring
    rw [e2]
    exact hsm
  · -- the Gaussian gradient bound
    have hm := hmain r hr1
    have hg := gaussTail'_eq (d := d) hS hσ hr0.le (ε' := ε')
    have h3 : Real.sqrt d * ((2 : ℝ) ^ ((d : ℝ) / 2) * e * Real.sqrt (obsEnergy d C₈ σ θ r)) ≤
        r ^ (-μ) := by
      have : Real.sqrt d * (2 : ℝ) ^ ((d : ℝ) / 2) * Real.sqrt (obsEnergy d C₈ σ θ r) * r ^ μ * e
          ≤ 1 := hT3
      have hinv : r ^ μ * r ^ (-μ) = 1 := by
        rw [← Real.rpow_add hr0]; simp
      have key : Real.sqrt d * ((2 : ℝ) ^ ((d : ℝ) / 2) * e * Real.sqrt (obsEnergy d C₈ σ θ r)) =
          (Real.sqrt d * (2 : ℝ) ^ ((d : ℝ) / 2) * Real.sqrt (obsEnergy d C₈ σ θ r) * r ^ μ * e) *
            r ^ (-μ) := by
        calc _ = Real.sqrt d * ((2 : ℝ) ^ ((d : ℝ) / 2) * e * Real.sqrt (obsEnergy d C₈ σ θ r)) *
              (r ^ μ * r ^ (-μ)) := by rw [hinv, mul_one]
          _ = _ := by ring
      rw [key]
      exact mul_le_of_le_one_left (Real.rpow_nonneg hr0.le _) this
    unfold obsGradient
    rw [hg, mul_add]
    have hsd := Real.sqrt_nonneg (d : ℝ)
    have := mul_le_mul_of_nonneg_left hm hsd
    calc _ ≤ Real.sqrt d * (K₁ * r ^ (-μ)) + r ^ (-μ) := add_le_add this h3
      _ = (Real.sqrt d * K₁ + 1) * r ^ (-μ) := by ring
  · have : Real.sqrt 2 * Q r * r ^ μ * r ^ (-a₁) * e ≤ 1 := hT1
    have hinv : r ^ μ * r ^ (-μ) = 1 := by rw [← Real.rpow_add hr0]; simp
    have hdiv : Real.sqrt 2 * obsError d C₈ κ D σ θ a₁ ε' δ r / r ^ a₁ ≤
        Real.sqrt 2 * (e * Q r) * r ^ (-a₁) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg hr0.le]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hEr (Real.sqrt_nonneg 2))
        (Real.rpow_nonneg hr0.le _)
    refine hdiv.trans ?_
    have key : Real.sqrt 2 * (e * Q r) * r ^ (-a₁) =
        (Real.sqrt 2 * Q r * r ^ μ * r ^ (-a₁) * e) * r ^ (-μ) := by
      calc _ = Real.sqrt 2 * (e * Q r) * r ^ (-a₁) * (r ^ μ * r ^ (-μ)) := by rw [hinv, mul_one]
        _ = _ := by ring
    rw [key]
    exact mul_le_of_le_one_left (Real.rpow_nonneg hr0.le _) this
  · have : Real.sqrt 2 * Q r * r ^ (a₁ * β) * r ^ (-a₁) * e ≤ 1 := hT2
    have e3 : (r ^ a₁) ^ (-β) = r ^ (-(a₁ * β)) := by
      rw [← Real.rpow_mul hr0.le]; ring_nf
    have hinv : r ^ (a₁ * β) * r ^ (-(a₁ * β)) = 1 := by rw [← Real.rpow_add hr0]; simp
    have hdiv : Real.sqrt 2 * obsError d C₈ κ D σ θ a₁ ε' δ r / r ^ a₁ ≤
        Real.sqrt 2 * (e * Q r) * r ^ (-a₁) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg hr0.le]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hEr (Real.sqrt_nonneg 2))
        (Real.rpow_nonneg hr0.le _)
    rw [e3]
    refine hdiv.trans ?_
    have key : Real.sqrt 2 * (e * Q r) * r ^ (-a₁) =
        (Real.sqrt 2 * Q r * r ^ (a₁ * β) * r ^ (-a₁) * e) * r ^ (-(a₁ * β)) := by
      calc _ = Real.sqrt 2 * (e * Q r) * r ^ (-a₁) * (r ^ (a₁ * β) * r ^ (-(a₁ * β))) := by
            rw [hinv, mul_one]
        _ = _ := by ring
    rw [key]
    exact mul_le_of_le_one_left (Real.rpow_nonneg hr0.le _) this

end QSH
