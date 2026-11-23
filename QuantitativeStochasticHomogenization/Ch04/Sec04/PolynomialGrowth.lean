import QuantitativeStochasticHomogenization.Front.Notation

/-!
# Functions of polynomial growth against Gaussian tails

A real function `f` has polynomial growth if `|f r| ≤ K r^N` for `r ≥ 1`. These functions are
closed under sums, products and square roots, and `f(r) e^{-c r^b} → 0` as `r → ∞` for `b, c > 0`.
This is the bookkeeping of the Gaussian error terms in the proof of Lemma 4.21 of
Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*.
-/

open Filter Topology

noncomputable section

namespace QSH

/-- **Polynomial growth**: `|f r| ≤ K r^N` for `r ≥ 1`. -/
def PolyGrowth (f : ℝ → ℝ) : Prop := ∃ K N : ℝ, 0 ≤ K ∧ ∀ r : ℝ, 1 ≤ r → |f r| ≤ K * r ^ N

theorem polyGrowth_const (c : ℝ) : PolyGrowth fun _ => c :=
  ⟨|c|, 0, abs_nonneg c, fun r _ => by rw [Real.rpow_zero, mul_one]⟩

theorem polyGrowth_rpow (a : ℝ) : PolyGrowth fun r => r ^ a :=
  ⟨1, a, zero_le_one, fun r hr => by
    rw [one_mul, abs_of_nonneg (Real.rpow_nonneg (zero_le_one.trans hr) a)]⟩

theorem polyGrowth_id : PolyGrowth fun r => r :=
  ⟨1, 1, zero_le_one, fun r hr => by
    rw [one_mul, Real.rpow_one, abs_of_nonneg (zero_le_one.trans hr)]⟩

theorem rpow_le_rpow_max_left {r : ℝ} (hr : 1 ≤ r) (a b : ℝ) : r ^ a ≤ r ^ max a b :=
  Real.rpow_le_rpow_of_exponent_le hr (le_max_left a b)

theorem rpow_le_rpow_max_right {r : ℝ} (hr : 1 ≤ r) (a b : ℝ) : r ^ b ≤ r ^ max a b :=
  Real.rpow_le_rpow_of_exponent_le hr (le_max_right a b)

theorem PolyGrowth.add {f g : ℝ → ℝ} (hf : PolyGrowth f) (hg : PolyGrowth g) :
    PolyGrowth fun r => f r + g r := by
  obtain ⟨K₁, N₁, hK₁, h₁⟩ := hf
  obtain ⟨K₂, N₂, hK₂, h₂⟩ := hg
  refine ⟨K₁ + K₂, max N₁ N₂, add_nonneg hK₁ hK₂, fun r hr => ?_⟩
  have e1 := mul_le_mul_of_nonneg_left (rpow_le_rpow_max_left hr N₁ N₂) hK₁
  have e2 := mul_le_mul_of_nonneg_left (rpow_le_rpow_max_right hr N₁ N₂) hK₂
  calc |f r + g r| ≤ |f r| + |g r| := abs_add_le _ _
    _ ≤ K₁ * r ^ N₁ + K₂ * r ^ N₂ := add_le_add (h₁ r hr) (h₂ r hr)
    _ ≤ K₁ * r ^ max N₁ N₂ + K₂ * r ^ max N₁ N₂ := add_le_add e1 e2
    _ = (K₁ + K₂) * r ^ max N₁ N₂ := by ring

theorem PolyGrowth.mul {f g : ℝ → ℝ} (hf : PolyGrowth f) (hg : PolyGrowth g) :
    PolyGrowth fun r => f r * g r := by
  obtain ⟨K₁, N₁, hK₁, h₁⟩ := hf
  obtain ⟨K₂, N₂, hK₂, h₂⟩ := hg
  refine ⟨K₁ * K₂, N₁ + N₂, mul_nonneg hK₁ hK₂, fun r hr => ?_⟩
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  rw [abs_mul, Real.rpow_add hr0]
  calc |f r| * |g r| ≤ (K₁ * r ^ N₁) * (K₂ * r ^ N₂) :=
        mul_le_mul (h₁ r hr) (h₂ r hr) (abs_nonneg _)
          (mul_nonneg hK₁ (Real.rpow_nonneg hr0.le _))
    _ = K₁ * K₂ * (r ^ N₁ * r ^ N₂) := by ring

theorem PolyGrowth.sqrt {f : ℝ → ℝ} (hf : PolyGrowth f) : PolyGrowth fun r => Real.sqrt (f r) := by
  obtain ⟨K, N, hK, h⟩ := hf
  refine ⟨Real.sqrt K, N / 2, Real.sqrt_nonneg K, fun r hr => ?_⟩
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  rw [abs_of_nonneg (Real.sqrt_nonneg _)]
  calc Real.sqrt (f r) ≤ Real.sqrt (K * r ^ N) :=
        Real.sqrt_le_sqrt ((le_abs_self _).trans (h r hr))
    _ = Real.sqrt K * r ^ (N / 2) := by
        rw [Real.sqrt_mul hK, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hr0.le]
        ring_nf

theorem PolyGrowth.of_le {f g : ℝ → ℝ} (hf : PolyGrowth f) (hle : ∀ r, 1 ≤ r → |g r| ≤ |f r|) :
    PolyGrowth g := by
  obtain ⟨K, N, hK, h⟩ := hf
  exact ⟨K, N, hK, fun r hr => (hle r hr).trans (h r hr)⟩

theorem PolyGrowth.const_mul {f : ℝ → ℝ} (hf : PolyGrowth f) (c : ℝ) :
    PolyGrowth fun r => c * f r :=
  (polyGrowth_const c).mul hf

/-- **Gaussian tails beat polynomial growth**: `f(r) e^{-c r^b} → 0`. -/
theorem PolyGrowth.tendsto_mul_exp_neg {f : ℝ → ℝ} (hf : PolyGrowth f) {b c : ℝ} (hb : 0 < b)
    (hc : 0 < c) : Tendsto (fun r => f r * Real.exp (-(c * r ^ b))) atTop (𝓝 0) := by
  obtain ⟨K, N, hK, h⟩ := hf
  have h1 : Tendsto (fun x : ℝ => x ^ (N / b) * Real.exp (-c * x)) atTop (𝓝 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (N / b) c hc
  have h2 := h1.comp (tendsto_rpow_atTop hb)
  have h3 : Tendsto (fun r : ℝ => K * (r ^ N * Real.exp (-(c * r ^ b)))) atTop (𝓝 0) := by
    have e : ∀ᶠ r : ℝ in atTop, ((fun x : ℝ => x ^ (N / b) * Real.exp (-c * x)) ∘
        fun r => r ^ b) r = r ^ N * Real.exp (-(c * r ^ b)) := by
      filter_upwards [eventually_gt_atTop 0] with r hr
      simp only [Function.comp]
      rw [← Real.rpow_mul hr.le, mul_div_cancel₀ N hb.ne', neg_mul]
    have := (h2.congr' e).const_mul K
    rwa [mul_zero] at this
  refine squeeze_zero_norm' ?_ h3
  filter_upwards [eventually_ge_atTop 1] with r hr
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (h r hr) (Real.exp_pos _).le

/-- **Eventually below any positive level.** -/
theorem PolyGrowth.eventually_mul_exp_neg_le {f : ℝ → ℝ} (hf : PolyGrowth f) {b c : ℝ}
    (hb : 0 < b) (hc : 0 < c) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ r in atTop, f r * Real.exp (-(c * r ^ b)) ≤ η :=
  ((hf.tendsto_mul_exp_neg hb hc).eventually_lt_const hη).mono fun _ h => h.le

/-- `r^a → ∞` eventually exceeds any level for `a > 0`. -/
theorem eventually_le_rpow {a : ℝ} (ha : 0 < a) (L : ℝ) : ∀ᶠ r : ℝ in atTop, L ≤ r ^ a :=
  (tendsto_rpow_atTop ha).eventually_ge_atTop L

/-- **Growth at most `r^N`**: `|f r| ≤ K r^N` for `r ≥ 1`. -/
def PowerBound (f : ℝ → ℝ) (N : ℝ) : Prop := ∃ K : ℝ, 0 ≤ K ∧ ∀ r : ℝ, 1 ≤ r → |f r| ≤ K * r ^ N

theorem PowerBound.polyGrowth {f : ℝ → ℝ} {N : ℝ} (h : PowerBound f N) : PolyGrowth f := by
  obtain ⟨K, hK, h⟩ := h
  exact ⟨K, N, hK, h⟩

theorem powerBound_const_mul_rpow (c a : ℝ) : PowerBound (fun r => c * r ^ a) a :=
  ⟨|c|, abs_nonneg c, fun r hr => by
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (zero_le_one.trans hr) a)]⟩

theorem powerBound_const (c : ℝ) : PowerBound (fun _ => c) 0 :=
  ⟨|c|, abs_nonneg c, fun r _ => by rw [Real.rpow_zero, mul_one]⟩

theorem PowerBound.mono {f : ℝ → ℝ} {N N' : ℝ} (h : PowerBound f N) (hN : N ≤ N') :
    PowerBound f N' := by
  obtain ⟨K, hK, h⟩ := h
  exact ⟨K, hK, fun r hr => (h r hr).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hr hN) hK)⟩

theorem PowerBound.of_le {f g : ℝ → ℝ} {N : ℝ} (h : PowerBound f N)
    (hle : ∀ r, 1 ≤ r → |g r| ≤ |f r|) : PowerBound g N := by
  obtain ⟨K, hK, h⟩ := h
  exact ⟨K, hK, fun r hr => (hle r hr).trans (h r hr)⟩

theorem PowerBound.congr {f g : ℝ → ℝ} {N : ℝ} (h : PowerBound f N)
    (he : ∀ r, 1 ≤ r → g r = f r) : PowerBound g N :=
  h.of_le fun r hr => by rw [he r hr]

theorem PowerBound.mul {f g : ℝ → ℝ} {N₁ N₂ : ℝ} (hf : PowerBound f N₁) (hg : PowerBound g N₂) :
    PowerBound (fun r => f r * g r) (N₁ + N₂) := by
  obtain ⟨K₁, hK₁, h₁⟩ := hf
  obtain ⟨K₂, hK₂, h₂⟩ := hg
  refine ⟨K₁ * K₂, mul_nonneg hK₁ hK₂, fun r hr => ?_⟩
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  rw [abs_mul, Real.rpow_add hr0]
  calc |f r| * |g r| ≤ (K₁ * r ^ N₁) * (K₂ * r ^ N₂) :=
        mul_le_mul (h₁ r hr) (h₂ r hr) (abs_nonneg _)
          (mul_nonneg hK₁ (Real.rpow_nonneg hr0.le _))
    _ = K₁ * K₂ * (r ^ N₁ * r ^ N₂) := by ring

theorem PowerBound.add {f g : ℝ → ℝ} {N : ℝ} (hf : PowerBound f N) (hg : PowerBound g N) :
    PowerBound (fun r => f r + g r) N := by
  obtain ⟨K₁, hK₁, h₁⟩ := hf
  obtain ⟨K₂, hK₂, h₂⟩ := hg
  refine ⟨K₁ + K₂, add_nonneg hK₁ hK₂, fun r hr => ?_⟩
  calc |f r + g r| ≤ |f r| + |g r| := abs_add_le _ _
    _ ≤ K₁ * r ^ N + K₂ * r ^ N := add_le_add (h₁ r hr) (h₂ r hr)
    _ = (K₁ + K₂) * r ^ N := by ring

theorem PowerBound.sqrt {f : ℝ → ℝ} {N : ℝ} (hf : PowerBound f N) :
    PowerBound (fun r => Real.sqrt (f r)) (N / 2) := by
  obtain ⟨K, hK, h⟩ := hf
  refine ⟨Real.sqrt K, Real.sqrt_nonneg K, fun r hr => ?_⟩
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  rw [abs_of_nonneg (Real.sqrt_nonneg _)]
  calc Real.sqrt (f r) ≤ Real.sqrt (K * r ^ N) :=
        Real.sqrt_le_sqrt ((le_abs_self _).trans (h r hr))
    _ = Real.sqrt K * r ^ (N / 2) := by
        rw [Real.sqrt_mul hK, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hr0.le]
        ring_nf

/-- A power bound with a negative exponent gives the decay `K r^{-μ}`. -/
theorem PowerBound.le {f : ℝ → ℝ} {N : ℝ} (hf : PowerBound f N) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ r : ℝ, 1 ≤ r → f r ≤ K * r ^ N := by
  obtain ⟨K, hK, h⟩ := hf
  exact ⟨K, hK, fun r hr => (le_abs_self _).trans (h r hr)⟩

theorem PolyGrowth.pow {f : ℝ → ℝ} (hf : PolyGrowth f) (n : ℕ) :
    PolyGrowth fun r => f r ^ n := by
  induction n with
  | zero => simpa using polyGrowth_const 1
  | succ n ih =>
    refine (ih.mul hf).of_le fun r _ => ?_
    rw [pow_succ]

theorem PowerBound.pow {f : ℝ → ℝ} {N : ℝ} (hf : PowerBound f N) (n : ℕ) :
    PowerBound (fun r => f r ^ n) (n * N) := by
  induction n with
  | zero => simpa using powerBound_const 1
  | succ n ih =>
    refine ((ih.mul hf).congr fun r _ => by rw [pow_succ]).mono (le_of_eq ?_)
    push_cast
    ring

end QSH
