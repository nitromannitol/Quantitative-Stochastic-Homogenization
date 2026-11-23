import QuantitativeStochasticHomogenization.Ch04.Sec04.HeatShellGrowth
import QuantitativeStochasticHomogenization.Ch04.Sec04.LocalizationEstimateReductionMass
import QuantitativeStochasticHomogenization.Ch04.Sec01.J1HeatBounds
import QuantitativeStochasticHomogenization.Ch04.Sec01.J1HeatMeasurability
import QuantitativeStochasticHomogenization.AppA.AlmostSureOsBound

/-!
# Lemma 4.21 from ball-growth estimates on a good event

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Lemma 4.21 and the proof of Proposition 4.11. The localization error
`|J₁(Φ_{z,r}, p, q) - J₁^{(δ)}(z, r, p, q)|` is at most a deterministic constant for
`|p|, |q| ≤ 1`. When the hypotheses of `abs_J1Heat_sub_localizedJ1_le_of_ball_growth` hold
with Gaussian energies at most `E` and ball-growth constant `A`, it is at most
`K (exp(-T²/(8r²)) + (heatShellConstant d k · A)^{1/2})` with `K` depending only on `d`, `Λ`
and `E`; the smallness conditions of that lemma are removed by the deterministic bound.

The stochastic estimate: suppose that above a random radius `X` with `X^γ ≤ O_s(C₁)` these
hypotheses hold with `A ≤ K₁ (Y² + r^{-2γ})` for a random variable `Y ≤ O_s(C₁ r^{-γ})`. Then the
localization error is at most
`Z = c (r^{-γ} X^γ + r^{-γ} + Y) ≤ O_s(C r^{-γ})` almost surely, since
`1_{X > r} ≤ r^{-γ} X^γ`. This gives `LocalizationApproximationUniform` and, with the almost
sure measurability of `J₁(Φ_{z,r}, p, q)`, the frozen statement (5.85).
-/

open MeasureTheory Filter

noncomputable section

namespace QSH

variable {d : ℕ}

/-! ## The deterministic bound -/

/-- The deterministic bound of the localization error for `|p|, |q| ≤ 1`. -/
def localizationCap (d : ℕ) (Λ : ℝ) : ℝ := Λ + 1 + ((d : ℝ) * d * Λ + d) ^ 2 / 2

theorem localizationCap_pos {Λ : ℝ} (hΛ : 0 ≤ Λ) : 0 < localizationCap d Λ := by
  unfold localizationCap
  positivity

theorem euclideanSq_le_one_of_euclideanNorm_le_one {p : Vec d} (hp : euclideanNorm p ≤ 1) :
    euclideanSq p ≤ 1 := by
  rw [← sq_euclideanNorm]
  exact pow_le_one₀ (zero_le_euclideanNorm p) hp

/-- **The deterministic bound of the localization error**: both energies lie in
`[0, Λ + 1]` and `[0, (d²Λ + d)²/2]` for `|p|, |q| ≤ 1`. -/
theorem abs_J1Heat_sub_localizedJ1_le_cap {Λ : ℝ} (hΛ : 0 ≤ Λ) {a : CoefficientField d Λ}
    {z : Vec d} {T r : ℝ} (hr : 0 < r) {S σ θ C : ℝ} (W : LocalizedBasis a z T S σ θ C)
    {p q : Vec d} (hp : euclideanNorm p ≤ 1) (hq : euclideanNorm q ≤ 1) :
    |J1Heat a z r p q - localizedJ1 W r p q| ≤ localizationCap d Λ := by
  obtain ⟨hJ0, hJ1, -⟩ := J1Heat_bounds a z r hr p q
  obtain ⟨hF0, hF1⟩ := localizedJ1_mem_Icc_linearCoefficient hΛ hr.ne' W p q
  have hL0 := linearCoefficient_nonneg hΛ p q
  have hL1 := linearCoefficient_le hΛ hp hq
  have hp1 := euclideanSq_le_one_of_euclideanNorm_le_one hp
  have hq1 := euclideanSq_le_one_of_euclideanNorm_le_one hq
  have h1 : Λ * euclideanSq p ≤ Λ := mul_le_of_le_one_right hΛ hp1
  have h2 : linearCoefficient d Λ p q ^ 2 ≤ ((d : ℝ) * d * Λ + d) ^ 2 :=
    pow_le_pow_left₀ hL0 hL1 2
  unfold localizationCap
  rw [abs_le]
  constructor <;> linarith

/-! ## The bound on the good event -/

theorem localizationErrorConstant_nonneg {Λ L : ℝ} (hΛ : 0 ≤ Λ) (hL : 0 ≤ L) :
    0 ≤ localizationErrorConstant d Λ L := by
  unfold localizationErrorConstant
  have hdΛ : 0 ≤ (d : ℝ) * Λ := mul_nonneg (Nat.cast_nonneg d) hΛ
  have hd2Λ : 0 ≤ (d : ℝ) ^ 2 * Λ := mul_nonneg (sq_nonneg _) hΛ
  have h1 : 0 ≤ ((d : ℝ) * Λ / 2 + L / 2) * (d * (2 * L + 1) ^ 2) :=
    mul_nonneg (by linarith) (mul_nonneg (Nat.cast_nonneg d) (sq_nonneg _))
  have h2 : 0 ≤ L / 2 * (2 : ℝ) ^ ((d : ℝ) / 2) := mul_nonneg (by linarith) (by positivity)
  have h3 : 0 ≤ (d : ℝ) ^ 2 * Λ * (2 * (2 * L + 1) + 1) / 2 + L :=
    add_nonneg (div_nonneg (mul_nonneg hd2Λ (by linarith)) (by norm_num)) hL
  linarith

theorem localizationErrorConstant_mono {Λ L L' : ℝ} (hΛ : 0 ≤ Λ) (hL : 0 ≤ L) (hLL : L ≤ L') :
    localizationErrorConstant d Λ L ≤ localizationErrorConstant d Λ L' := by
  unfold localizationErrorConstant
  have hdΛ : 0 ≤ (d : ℝ) * Λ := mul_nonneg (Nat.cast_nonneg d) hΛ
  have hd2Λ : 0 ≤ (d : ℝ) ^ 2 * Λ := mul_nonneg (sq_nonneg _) hΛ
  have h1 : ((d : ℝ) * Λ / 2 + L / 2) * (d * (2 * L + 1) ^ 2) ≤
      ((d : ℝ) * Λ / 2 + L' / 2) * (d * (2 * L' + 1) ^ 2) :=
    mul_le_mul (by linarith)
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) (by linarith) 2)
        (Nat.cast_nonneg d))
      (mul_nonneg (Nat.cast_nonneg d) (sq_nonneg _)) (by linarith)
  have h2 : L / 2 * (2 : ℝ) ^ ((d : ℝ) / 2) ≤ L' / 2 * (2 : ℝ) ^ ((d : ℝ) / 2) :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have h3 : (d : ℝ) ^ 2 * Λ * (2 * (2 * L + 1) + 1) ≤ (d : ℝ) ^ 2 * Λ * (2 * (2 * L' + 1) + 1) :=
    mul_le_mul_of_nonneg_left (by linarith) hd2Λ
  linarith

/-- The constant of `abs_J1Heat_sub_localizedJ1_le_of_ballGrowthData`, with
`L = d²Λ + d`, `m = heatGramConstant d` and `c = (m/4)^{1/2}/d`. -/
def ballGrowthLocalizationConstant (d : ℕ) (Λ E : ℝ) : ℝ :=
  localizationCap d Λ * (2 * ((d : ℝ) * d * Λ + d) ^ 2 * (2 : ℝ) ^ ((d : ℝ) / 2)) +
    localizationErrorConstant d Λ ((d : ℝ) * d * Λ + d) *
      ((2 : ℝ) ^ ((d : ℝ) / 2) * (d * E / heatGramConstant d) + 1) +
    localizationCap d Λ / (Real.sqrt (heatGramConstant d / 4) / d / 2) +
    (localizationCap d Λ + localizationErrorConstant d Λ ((d : ℝ) * d * Λ + d)) *
      (2 * (2 * ((d : ℝ) * d * Λ + d) + 1) / (Real.sqrt (heatGramConstant d / 4) / d))

/-- The pathwise hypotheses of `abs_J1Heat_sub_localizedJ1_le_of_ball_growth` at a coefficient
field `a`: corrector potentials `φ_i` with gradients `g_i` solving `-∇·a(e_i + g_i) = 0`, small
oscillation on `B_r(z)`, Gaussian energies of `W_i = e_i + g_i` at scale `√2 r` at most `E`, the
first-order Liouville representation of `A₁` by the `W_i`, and slopes `b` with
`∑ b_{ij}² ≤ 1/4` such that the gradients of the localized coordinates satisfy
`∫_{B_T(z) ∩ B_t(z)} |∇w_i - W_i - ∑_j b_{ij} W_j|² ≤ A (t/r)^k |B_t|` for every `t ≥ r`. -/
def LocalizationBallGrowthData {Λ : ℝ} (a : CoefficientField d Λ) (z : Vec d) (T r : ℝ)
    {S σ θ C : ℝ} (B : LocalizedBasis a z T S σ θ C) (k : ℕ) (E A : ℝ) : Prop :=
  ∃ (φ : Fin d → Vec d → ℝ) (g : Fin d → Vec d → Vec d),
    (∀ i, HasWeakGradient Set.univ (φ i) (g i)) ∧
    (∀ i, ∀ R : ℝ, 0 < R → MemLp (φ i) 2 (volume.restrict (ball 0 R)) ∧
      MemLp (g i) 2 (volume.restrict (ball 0 R))) ∧
    (∀ i, HasWeakDivergence Set.univ (fun x => (a x).mulVec (unitVector i + g i x))
      (fun _ => 0)) ∧
    (∃ (c : Fin d → ℝ) (ε : ℝ), (d : ℝ) * ε ^ 2 ≤ (1 / 4 : ℝ) ^ d / 16 ∧
      ∀ i, ∫ x in ball z r, (φ i x - c i) ^ 2 ≤ ε ^ 2 * r ^ 2 * volume.real (ball z r)) ∧
    (∀ i, Integrable (fun x => heatKernel z (Real.sqrt 2 * r) x *
      euclideanSq (unitVector i + g i x))) ∧
    (∀ i, ∫ x, heatKernel z (Real.sqrt 2 * r) x * euclideanSq (unitVector i + g i x) ≤ E) ∧
    (∀ w : HarmonicA1 a, ∃ ξ : Vec d,
      ∀ᵐ x, w.grad x = ∑ i, ξ i • (unitVector i + g i x)) ∧
    (∀ ξ : Vec d, ∃ w : HarmonicA1 a,
      ∀ᵐ x, w.grad x = ∑ i, ξ i • (unitVector i + g i x)) ∧
    ∃ b : Fin d → Fin d → ℝ, ∑ i, ∑ j, b i j ^ 2 ≤ 1 / 4 ∧
      ∀ i, ∀ t : ℝ, r ≤ t → ∫ x in ball z T ∩ ball z t,
        euclideanSq ((B.coordinate i).grad x -
          ((unitVector i + g i x) + ∑ j, b i j • (unitVector j + g j x))) ≤
            A * (t / r) ^ k * volume.real (ball z t)

theorem le_four_mul_add_of_le {x k₁ k₂ k₃ k₄ e ρ : ℝ} (h₁ : 0 ≤ k₁) (h₂ : 0 ≤ k₂)
    (h₃ : 0 ≤ k₃) (h₄ : 0 ≤ k₄) (he : 0 ≤ e) (hρ : 0 ≤ ρ)
    (hx : x ≤ k₁ * e + k₂ * e + k₃ * ρ + k₄ * ρ) : x ≤ (k₁ + k₂ + k₃ + k₄) * (e + ρ) := by
  have hexp : (k₁ + k₂ + k₃ + k₄) * (e + ρ) =
      k₁ * e + k₂ * e + k₃ * ρ + k₄ * ρ + (k₁ * ρ + k₂ * ρ + k₃ * e + k₄ * e) := by ring
  rw [hexp]
  linarith [mul_nonneg h₁ hρ, mul_nonneg h₂ hρ, mul_nonneg h₃ he, mul_nonneg h₄ he]

/-- **Lemmas 4.21-4.22 on the good event with a uniform constant**: under
`LocalizationBallGrowthData`, the localization error is at most
`K (exp(-T²/(8r²)) + (heatShellConstant d k · A)^{1/2})`, `K = ballGrowthLocalizationConstant d Λ E`,
for `|p|, |q| ≤ 1`. -/
theorem abs_J1Heat_sub_localizedJ1_le_of_ballGrowthData {Λ : ℝ} {a : CoefficientField d Λ}
    (hΛ : 0 ≤ Λ) (hd : 0 < d) {z : Vec d} {T r : ℝ} (hr : 0 < r) (hrT : r ≤ T) {S σ θ C : ℝ}
    {B : LocalizedBasis a z T S σ θ C} {p q : Vec d} (hp : euclideanNorm p ≤ 1)
    (hq : euclideanNorm q ≤ 1) {k : ℕ} {E A : ℝ} (hE0 : 0 ≤ E) (hA : 0 ≤ A)
    (h : LocalizationBallGrowthData a z T r B k E A) :
    |J1Heat a z r p q - localizedJ1 B r p q| ≤ ballGrowthLocalizationConstant d Λ E *
      (Real.exp (-(T ^ 2) / (8 * r ^ 2)) + Real.sqrt (heatShellConstant d k * A)) := by
  obtain ⟨φ, g, hφg, hloc, harm, ⟨c, ε, hε, hosc⟩, hW, hE, hrep, hWmem, b, hb, hgrowth⟩ := h
  have he0 : 0 ≤ Real.exp (-(T ^ 2) / (8 * r ^ 2)) := (Real.exp_pos _).le
  have hρ0 : 0 ≤ Real.sqrt (heatShellConstant d k * A) := Real.sqrt_nonneg _
  have hL0 : 0 ≤ linearCoefficient d Λ p q := linearCoefficient_nonneg hΛ p q
  have hLL₀ : linearCoefficient d Λ p q ≤ (d : ℝ) * d * Λ + d := linearCoefficient_le hΛ hp hq
  have hL₀0 : 0 ≤ (d : ℝ) * d * Λ + d := hL0.trans hLL₀
  have hm0 : 0 < heatGramConstant d := heatGramConstant_pos d
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hcc0 : 0 < Real.sqrt (heatGramConstant d / 4) / d :=
    div_pos (Real.sqrt_pos.mpr (by positivity)) hdR
  have hcap0 : 0 < localizationCap d Λ := localizationCap_pos hΛ
  have hE₀0 : 0 ≤ localizationErrorConstant d Λ ((d : ℝ) * d * Λ + d) :=
    localizationErrorConstant_nonneg hΛ hL₀0
  have hcapb : |J1Heat a z r p q - localizedJ1 B r p q| ≤ localizationCap d Λ :=
    abs_J1Heat_sub_localizedJ1_le_cap hΛ hr B hp hq
  have h2d : 0 < (2 : ℝ) ^ ((d : ℝ) / 2) := by positivity
  have hk10 : 0 ≤ localizationCap d Λ * (2 * ((d : ℝ) * d * Λ + d) ^ 2 *
      (2 : ℝ) ^ ((d : ℝ) / 2)) := by positivity
  have hk20 : 0 ≤ localizationErrorConstant d Λ ((d : ℝ) * d * Λ + d) *
      ((2 : ℝ) ^ ((d : ℝ) / 2) * (d * E / heatGramConstant d) + 1) := by positivity
  have hk30 : 0 ≤ localizationCap d Λ / (Real.sqrt (heatGramConstant d / 4) / d / 2) := by
    positivity
  have hk40 : 0 ≤ (localizationCap d Λ + localizationErrorConstant d Λ ((d : ℝ) * d * Λ + d)) *
      (2 * (2 * ((d : ℝ) * d * Λ + d) + 1) / (Real.sqrt (heatGramConstant d / 4) / d)) := by
    positivity
  unfold ballGrowthLocalizationConstant
  refine le_four_mul_add_of_le hk10 hk20 hk30 hk40 he0 hρ0 ?_
  set e := Real.exp (-(T ^ 2) / (8 * r ^ 2)) with he_def
  set ρ := Real.sqrt (heatShellConstant d k * A) with hρ_def
  set L := linearCoefficient d Λ p q with hL_def
  set L₀ : ℝ := (d : ℝ) * d * Λ + d with hL₀_def
  set m := heatGramConstant d with hm_def
  set cc := Real.sqrt (m / 4) / d with hcc_def
  set cap := localizationCap d Λ with hcap_def
  set E₀ := localizationErrorConstant d Λ L₀ with hE₀_def
  have hke : 0 ≤ E₀ * ((2 : ℝ) ^ ((d : ℝ) / 2) * (d * E / m) + 1) * e := by positivity
  have hk1e : 0 ≤ cap * (2 * L₀ ^ 2 * (2 : ℝ) ^ ((d : ℝ) / 2)) * e := by positivity
  have hk3ρ : 0 ≤ cap / (cc / 2) * ρ := by positivity
  have hcapρ : 0 ≤ cap * (2 * (2 * L₀ + 1) / cc) * ρ := by positivity
  have hE₀ρ : 0 ≤ E₀ * (2 * (2 * L₀ + 1) / cc) * ρ := by positivity
  have hk4 : (cap + E₀) * (2 * (2 * L₀ + 1) / cc) * ρ =
      cap * (2 * (2 * L₀ + 1) / cc) * ρ + E₀ * (2 * (2 * L₀ + 1) / cc) * ρ := by ring
  rw [hk4]
  by_cases hsmall : L ^ 2 / 2 * ((2 : ℝ) ^ ((d : ℝ) / 2) * e) ≤ 1 / 4
  · by_cases hρc : ρ ≤ cc / 2
    · have hmain := abs_J1Heat_sub_localizedJ1_le_of_ball_growth hΛ hd hr hrT hsmall φ g hφg
        hloc harm c hosc hε hE0 hW hE hrep hWmem b hb hA k hgrowth hρc
      have hηle : 2 * (2 * L + 1) * ρ / cc ≤ 2 * (2 * L₀ + 1) / cc * ρ := by
        rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hcc0]
        gcongr
      have hη0 : 0 ≤ 2 * (2 * L + 1) * ρ / cc := by positivity
      by_cases hη1 : 2 * (2 * L + 1) * ρ / cc ≤ 1
      · have hκ0 : 0 ≤ (2 : ℝ) ^ ((d : ℝ) / 2) * e * (d * E / m) := by positivity
        have hb2 := localizationErrorBound_le hΛ p q (T := T) (r := r) hη0 hη1 hκ0
        have hE₀L : localizationErrorConstant d Λ L ≤ E₀ :=
          localizationErrorConstant_mono (d := d) hΛ hL0 hLL₀
        have hsum0 : 0 ≤ (2 : ℝ) ^ ((d : ℝ) / 2) * e * (d * E / m) + e +
            2 * (2 * L + 1) * ρ / cc := by positivity
        have h3 := mul_le_mul_of_nonneg_right hE₀L hsum0
        have h4 := mul_le_mul_of_nonneg_left hηle hE₀0
        have h5 : E₀ * ((2 : ℝ) ^ ((d : ℝ) / 2) * e * (d * E / m) + e +
            2 * (2 * L + 1) * ρ / cc) = E₀ * ((2 : ℝ) ^ ((d : ℝ) / 2) * (d * E / m) + 1) * e +
              E₀ * (2 * (2 * L + 1) * ρ / cc) := by ring
        have h6 : E₀ * (2 * (2 * L₀ + 1) / cc * ρ) = E₀ * (2 * (2 * L₀ + 1) / cc) * ρ := by ring
        have hmain' : |J1Heat a z r p q - localizedJ1 B r p q| ≤
            localizationErrorConstant d Λ L * ((2 : ℝ) ^ ((d : ℝ) / 2) * e * (d * E / m) + e +
              2 * (2 * L + 1) * ρ / cc) := hmain.trans hb2
        linarith
      · have hη1' := (not_le.mp hη1).le
        have h1 : cap ≤ cap * (2 * (2 * L + 1) * ρ / cc) := le_mul_of_one_le_right hcap0.le hη1'
        have h2 := mul_le_mul_of_nonneg_left hηle hcap0.le
        have h3 : cap * (2 * (2 * L₀ + 1) / cc * ρ) = cap * (2 * (2 * L₀ + 1) / cc) * ρ := by
          ring
        linarith
    · have hρc' := (not_le.mp hρc).le
      have h1 : cap ≤ cap / (cc / 2) * ρ := by
        rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
        exact mul_le_mul_of_nonneg_left hρc' hcap0.le
      linarith
  · have hsmall' := not_le.mp hsmall
    have hL2 : L ^ 2 ≤ L₀ ^ 2 := pow_le_pow_left₀ hL0 hLL₀ 2
    have h0 : L ^ 2 * ((2 : ℝ) ^ ((d : ℝ) / 2) * e) ≤ L₀ ^ 2 * ((2 : ℝ) ^ ((d : ℝ) / 2) * e) :=
      mul_le_mul_of_nonneg_right hL2 (by positivity)
    have h1 : 1 ≤ 2 * L₀ ^ 2 * (2 : ℝ) ^ ((d : ℝ) / 2) * e := by linarith
    have h2 := mul_le_mul_of_nonneg_left h1 hcap0.le
    have h3 : cap * (2 * L₀ ^ 2 * (2 : ℝ) ^ ((d : ℝ) / 2) * e) =
        cap * (2 * L₀ ^ 2 * (2 : ℝ) ^ ((d : ℝ) / 2)) * e := by ring
    linarith

/-! ## The stochastic estimate -/

/-- **The ball-growth estimate of Lemma 4.21 on a good event** (the remaining analytic input of
(5.85)): there are `k`, `E ≥ 0`, `K₁ ≥ 0` and `C₁ > 0` such that for every law, every localized
family, center and scale `r ≥ 2` there are nonnegative random variables `X` and `Y` with
`X^γ ≤ O_s(C₁)` and `Y ≤ O_s(C₁ r^{-γ})`, and almost surely, if `X ≤ r`, then
`LocalizationBallGrowthData` holds with energy bound `E` and ball-growth constant
`K₁ (Y² + r^{-2γ})`. -/
def LocalizationBallGrowthEstimate (d : ℕ) (Λ s δ γ α σ θ C₀ : ℝ) : Prop :=
  ∃ (k : ℕ) (E K₁ C₁ : ℝ), 0 ≤ E ∧ 0 ≤ K₁ ∧ 0 < C₁ ∧
    ∀ P : Measure (CoefficientField d Λ), LawHypotheses P →
      ∀ (W : LocalizedFamily d Λ δ γ α σ θ C₀) (z : Vec d) (r : ℝ) (hr : 2 ≤ r),
        ∃ X Y : CoefficientField d Λ → ℝ, (∀ a, 0 ≤ X a) ∧ (∀ a, 0 ≤ Y a) ∧
          AEOsBound P (fun a => X a ^ γ) s C₁ ∧ AEOsBound P Y s (C₁ * r ^ (-γ)) ∧
          ∀ᵐ a ∂P, X a ≤ r →
            LocalizationBallGrowthData a z (localizationOuterRadius δ r) r (W a z r hr) k E
              (K₁ * (Y a ^ 2 + (r ^ (-γ)) ^ 2))

/-- `LocalizationBallGrowthEstimate` for the laws of a class `L`. -/
def LocalizationBallGrowthEstimateOn {d : ℕ} {Λ : ℝ} (L : Measure (CoefficientField d Λ) → Prop)
    (s δ γ α σ θ C₀ : ℝ) : Prop :=
  ∃ (k : ℕ) (E K₁ C₁ : ℝ), 0 ≤ E ∧ 0 ≤ K₁ ∧ 0 < C₁ ∧
    ∀ P : Measure (CoefficientField d Λ), L P →
      ∀ (W : LocalizedFamily d Λ δ γ α σ θ C₀) (z : Vec d) (r : ℝ) (hr : 2 ≤ r),
        ∃ X Y : CoefficientField d Λ → ℝ, (∀ a, 0 ≤ X a) ∧ (∀ a, 0 ≤ Y a) ∧
          AEOsBound P (fun a => X a ^ γ) s C₁ ∧ AEOsBound P Y s (C₁ * r ^ (-γ)) ∧
          ∀ᵐ a ∂P, X a ≤ r →
            LocalizationBallGrowthData a z (localizationOuterRadius δ r) r (W a z r hr) k E
              (K₁ * (Y a ^ 2 + (r ^ (-γ)) ^ 2))

/-- `LocalizationApproximationUniform` for the laws of a class `L`. -/
def LocalizationApproximationUniformOn {d : ℕ} {Λ : ℝ}
    (L : Measure (CoefficientField d Λ) → Prop) (s δ γ α σ θ C₀ C : ℝ) : Prop :=
  ∀ P : Measure (CoefficientField d Λ), L P →
    ∀ W : LocalizedFamily d Λ δ γ α σ θ C₀, ∀ (z : Vec d) (r : ℝ) (hr : 2 ≤ r) (p q : Vec d),
      euclideanNorm p < 1 → euclideanNorm q < 1 →
      ∃ Z : CoefficientField d Λ → ℝ,
        AEOsBound P Z s (C * r ^ (-γ)) ∧
        ∀ᵐ a ∂P, (∃ η κ : ℝ, LocalizationApproximationAtUniform a z
            (localizationOuterRadius δ r) r (by linarith : r ≠ 0) (W a z r hr) p q η κ (Z a)) ∨
          |J1Heat a z r p q - localizedJ1 (W a z r hr) r p q| ≤ Z a

theorem exp_neg_localizationOuterRadius_le {δ γ R₀ : ℝ} (hγ : 0 ≤ γ) (hR₀ : 0 < R₀)
    (hexp : ∀ r : ℝ, R₀ ≤ r →
      Real.exp (-(localizationOuterRadius δ r ^ 2) / (8 * r ^ 2)) ≤ r ^ (-γ))
    {r : ℝ} (hr : 0 < r) :
    Real.exp (-(localizationOuterRadius δ r ^ 2) / (8 * r ^ 2)) ≤ (1 + R₀ ^ γ) * r ^ (-γ) := by
  have hrγ : 0 < r ^ (-γ) := Real.rpow_pos_of_pos hr _
  have hRγ : 0 ≤ R₀ ^ γ := Real.rpow_nonneg hR₀.le _
  by_cases hrR : R₀ ≤ r
  · have := hexp r hrR
    linarith [mul_nonneg hRγ hrγ.le]
  · replace hrR := not_le.mp hrR
    have h1 : Real.exp (-(localizationOuterRadius δ r ^ 2) / (8 * r ^ 2)) ≤ 1 := by
      rw [Real.exp_le_one_iff, neg_div]
      exact neg_nonpos.mpr (by positivity)
    have h2 : 1 ≤ R₀ ^ γ * r ^ (-γ) := by
      rw [Real.rpow_neg hr.le, ← div_eq_mul_inv, ← Real.div_rpow hR₀.le hr.le]
      exact Real.one_le_rpow ((one_le_div hr).mpr hrR.le) hγ
    linarith

theorem sqrt_mul_sq_add_sq_le {H y t : ℝ} (hH : 0 ≤ H) (hy : 0 ≤ y) (ht : 0 ≤ t) :
    Real.sqrt (H * (y ^ 2 + t ^ 2)) ≤ Real.sqrt H * (y + t) := by
  rw [Real.sqrt_mul hH]
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg H)
  calc Real.sqrt (y ^ 2 + t ^ 2) ≤ Real.sqrt ((y + t) ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith [mul_nonneg hy ht])
    _ = y + t := Real.sqrt_sq (by positivity)

/-- **The stochastic form of Lemmas 4.21-4.22 from the ball-growth estimate**: on `{X ≤ r}` the
localization error is at most `K (exp(-T²/(8r²)) + √(heatShellConstant d k · A))`, off it at
most `localizationCap d Λ ≤ localizationCap d Λ · r^{-γ} X^γ`. -/
theorem localizationApproximationUniformOn_of_ballGrowthOn {Λ s δ γ α σ θ C₀ : ℝ}
    {L : Measure (CoefficientField d Λ) → Prop} (hLP : ∀ P, L P → LawHypotheses P) (hd : 0 < d)
    (hΛ : 0 ≤ Λ) (hs : 1 ≤ s) (hδ : 0 < δ) (hγ : 0 ≤ γ)
    (h : LocalizationBallGrowthEstimateOn L s δ γ α σ θ C₀) :
    ∃ C : ℝ, 0 < C ∧ LocalizationApproximationUniformOn L s δ γ α σ θ C₀ C := by
  obtain ⟨k, E, K₁, C₁, hE, hK₁, hC₁, hmain⟩ := h
  obtain ⟨R₀, hR₀, hexp⟩ := exists_exp_neg_le_rpow hδ γ
  set cap := localizationCap d Λ with hcap_def
  set Kb := ballGrowthLocalizationConstant d Λ E with hKb_def
  have hcap0 : 0 < cap := localizationCap_pos hΛ
  have hsc0 : 0 ≤ heatShellConstant d k := by
    unfold heatShellConstant heatShellSum
    exact mul_nonneg (mul_nonneg (by positivity) measureReal_nonneg)
      (tsum_nonneg fun j => by positivity)
  set H := Real.sqrt (heatShellConstant d k * K₁) with hH_def
  have hH0 : 0 ≤ H := Real.sqrt_nonneg _
  have hRγ : 0 ≤ R₀ ^ γ := Real.rpow_nonneg hR₀.le _
  have hKb0 : 0 ≤ Kb := by
    -- every term of the constant is nonnegative
    have hm0 : 0 < heatGramConstant d := heatGramConstant_pos d
    have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd
    have hL₀ : 0 ≤ (d : ℝ) * d * Λ + d := by positivity
    have hE₀ := localizationErrorConstant_nonneg (d := d) hΛ hL₀
    have hcc : 0 < Real.sqrt (heatGramConstant d / 4) / d :=
      div_pos (Real.sqrt_pos.mpr (by positivity)) hdR
    rw [hKb_def, ballGrowthLocalizationConstant]
    positivity
  set c₀ := Kb * (1 + R₀ ^ γ) + Kb * H + 1 with hc₀_def
  set cY := Kb * H + 1 with hcY_def
  have hc₀ : 0 < c₀ := by positivity
  have hcY : 0 < cY := by positivity
  have hl2 : 0 < Real.log 2 ^ s⁻¹ := Real.rpow_pos_of_pos (Real.log_pos one_lt_two) _
  refine ⟨cap * C₁ + c₀ / Real.log 2 ^ s⁻¹ + cY * C₁, by positivity, ?_⟩
  intro P hLP' W z r hr p q hp hq
  have : IsProbabilityMeasure P := (hLP P hLP').1
  have hr0 : 0 < r := by linarith
  have hrγ : 0 < r ^ (-γ) := Real.rpow_pos_of_pos hr0 _
  obtain ⟨X, Y, hX0, hY0, hXos, hYos, hae⟩ := hmain P hLP' W z r hr
  refine ⟨fun a => cap * r ^ (-γ) * X a ^ γ + c₀ * r ^ (-γ) + cY * Y a, ?_, ?_⟩
  · have h1 := hXos.const_mul (mul_pos hcap0 hrγ)
    have h2 : AEOsBound P (fun _ => c₀ * r ^ (-γ)) s (c₀ * r ^ (-γ) / Real.log 2 ^ s⁻¹) :=
      (osBound_of_le_const measurable_const (by linarith) (mul_pos hc₀ hrγ)
        (Eventually.of_forall fun _ => le_rfl)).aeOsBound_of_ae_eq EventuallyEq.rfl
    have h3 := hYos.const_mul hcY
    refine ((h1.add h2 hs).add h3 hs).mono_scale (le_of_eq ?_)
    ring
  · filter_upwards [hae] with a ha
    right
    have hp1 : euclideanNorm p ≤ 1 := hp.le
    have hq1 : euclideanNorm q ≤ 1 := hq.le
    have hXγ : 0 ≤ X a ^ γ := Real.rpow_nonneg (hX0 a) _
    have hZ1 : 0 ≤ cap * r ^ (-γ) * X a ^ γ := by positivity
    have hZ3 : 0 ≤ cY * Y a := mul_nonneg hcY.le (hY0 a)
    by_cases hXr : X a ≤ r
    · have hrT : r ≤ localizationOuterRadius δ r := by
        unfold localizationOuterRadius
        calc r = r ^ (1 : ℝ) := (Real.rpow_one r).symm
          _ ≤ r ^ (1 + δ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      have hA0 : 0 ≤ K₁ * (Y a ^ 2 + (r ^ (-γ)) ^ 2) := by positivity
      have hb := abs_J1Heat_sub_localizedJ1_le_of_ballGrowthData hΛ hd hr0 hrT hp1 hq1 hE hA0
        (ha hXr)
      have he := exp_neg_localizationOuterRadius_le hγ hR₀ hexp hr0 (δ := δ)
      have hρ : Real.sqrt (heatShellConstant d k * (K₁ * (Y a ^ 2 + (r ^ (-γ)) ^ 2))) ≤
          H * (Y a + r ^ (-γ)) := by
        rw [← mul_assoc]
        exact sqrt_mul_sq_add_sq_le (mul_nonneg hsc0 hK₁) (hY0 a) hrγ.le
      have hsum : Real.exp (-(localizationOuterRadius δ r ^ 2) / (8 * r ^ 2)) +
          Real.sqrt (heatShellConstant d k * (K₁ * (Y a ^ 2 + (r ^ (-γ)) ^ 2))) ≤
          (1 + R₀ ^ γ) * r ^ (-γ) + H * (Y a + r ^ (-γ)) := add_le_add he hρ
      have hfin : Kb * ((1 + R₀ ^ γ) * r ^ (-γ) + H * (Y a + r ^ (-γ))) ≤
          c₀ * r ^ (-γ) + cY * Y a := by
        have hdiff : c₀ * r ^ (-γ) + cY * Y a -
            Kb * ((1 + R₀ ^ γ) * r ^ (-γ) + H * (Y a + r ^ (-γ))) = r ^ (-γ) + Y a := by
          rw [hc₀_def, hcY_def]
          ring
        linarith [hY0 a]
      calc |J1Heat a z r p q - localizedJ1 (W a z r hr) r p q|
          ≤ Kb * (Real.exp (-(localizationOuterRadius δ r ^ 2) / (8 * r ^ 2)) +
            Real.sqrt (heatShellConstant d k * (K₁ * (Y a ^ 2 + (r ^ (-γ)) ^ 2)))) := hb
        _ ≤ Kb * ((1 + R₀ ^ γ) * r ^ (-γ) + H * (Y a + r ^ (-γ))) :=
            mul_le_mul_of_nonneg_left hsum hKb0
        _ ≤ c₀ * r ^ (-γ) + cY * Y a := hfin
        _ ≤ cap * r ^ (-γ) * X a ^ γ + c₀ * r ^ (-γ) + cY * Y a := by linarith
    · replace hXr := not_le.mp hXr
      have h1 : 1 ≤ r ^ (-γ) * X a ^ γ := by
        rw [Real.rpow_neg hr0.le, inv_mul_eq_div, ← Real.div_rpow (hX0 a) hr0.le]
        exact Real.one_le_rpow ((one_le_div hr0).mpr hXr.le) hγ
      have h2 : cap ≤ cap * r ^ (-γ) * X a ^ γ := by
        rw [mul_assoc]
        exact le_mul_of_one_le_right hcap0.le h1
      have hc := abs_J1Heat_sub_localizedJ1_le_cap hΛ hr0 (W a z r hr) hp1 hq1
      have hc0r : 0 ≤ c₀ * r ^ (-γ) := by positivity
      linarith

theorem localizationApproximationUniform_of_ballGrowth {Λ s δ γ α σ θ C₀ : ℝ} (hd : 0 < d)
    (hΛ : 0 ≤ Λ) (hs : 1 ≤ s) (hδ : 0 < δ) (hγ : 0 ≤ γ)
    (h : LocalizationBallGrowthEstimate d Λ s δ γ α σ θ C₀) :
    ∃ C : ℝ, 0 < C ∧ LocalizationApproximationUniform d Λ s δ γ α σ θ C₀ C :=
  localizationApproximationUniformOn_of_ballGrowthOn (L := LawHypotheses) (fun _ h => h) hd hΛ hs
    hδ hγ h

/-! ## The frozen statement (5.85) -/

theorem subsingleton_coefficientField_of_neg {Λ : ℝ} (hΛ : Λ < 0) :
    Subsingleton (CoefficientField d Λ) := by
  refine ⟨fun a b => ?_⟩
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    cases a
    cases b
    congr
    funext x i
    exact Fin.elim0 i
  · exfalso
    have h := a.elliptic 0 (fun _ => 1)
    have hsq : euclideanSq (fun _ : Fin d => (1 : ℝ)) = d := by
      simp [euclideanSq, dot]
    rw [hsq] at h
    have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd
    linarith [h.1, h.2, mul_neg_of_neg_of_pos hΛ hdR]

/-- The almost sure measurability of `J₁(Φ_{z,r}, p, q)` for every law. -/
theorem aemeasurable_J1Heat_of_lawHypotheses (d : ℕ) (Λ : ℝ)
    (P : Measure (CoefficientField d Λ)) (hP : LawHypotheses P) (z : Vec d) (r : ℝ)
    (p q : Vec d) (hr : 2 ≤ r) : AEMeasurable (fun a => J1Heat a z r p q) P := by
  have : IsProbabilityMeasure P := hP.1
  by_cases hΛ : 0 ≤ Λ
  · exact (aestronglyMeasurable_J1Heat hΛ P z r (by linarith) p q).aemeasurable
  · have := subsingleton_coefficientField_of_neg (d := d) (not_le.mp hΛ)
    exact Subsingleton.measurable.aemeasurable

/-- **(5.85) from the ball-growth estimate of Lemma 4.21.** For every window of exponents, a
choice of the structural constants `α, σ, θ, C₀` with `LocalizationBallGrowthEstimate` gives the
frozen statement `QSH.Frozen.localizedEnergy`. -/
theorem localizedEnergy_of_ballGrowth
    (h : ∀ (d : ℕ), 2 ≤ d → ∀ Λ s δ γ : ℝ,
      1 < Λ → 1 < s → s < 2 → 0 < δ →
      (d : ℝ) / 2 * (1 + δ) < γ →
      γ < min ((d : ℝ) / s) ((d : ℝ) / 2 * (1 + δ) + δ) →
      ∃ α σ θ C₀ : ℝ, 0 < α ∧ α ≤ (d : ℝ) / 2 ∧ γ < α * (1 + δ) + δ ∧
        0 < σ ∧ σ ≤ 1 / 2 ∧ 0 < θ ∧ θ ≤ 1 / 2 ∧ 0 < C₀ ∧
        LocalizationBallGrowthEstimate d Λ s δ γ α σ θ C₀) :
    QSH.Frozen.localizedEnergy :=
  localizedEnergy_of_uniformApproximation aemeasurable_J1Heat_of_lawHypotheses
    fun d hd Λ s δ γ hΛ hs1 hs2 hδ hγ1 hγ2 => by
      obtain ⟨α, σ, θ, C₀, hα, hαd, hαγ, hσ, hσ2, hθ, hθ2, hC₀, hest⟩ :=
        h d hd Λ s δ γ hΛ hs1 hs2 hδ hγ1 hγ2
      have hγ0 : 0 ≤ γ := le_trans (by positivity) hγ1.le
      obtain ⟨C, hC, happ⟩ := localizationApproximationUniform_of_ballGrowth (by omega)
        (by linarith) hs1.le hδ hγ0 hest
      exact ⟨α, σ, θ, C₀, C, ⟨hα, hαd, hαγ, hσ, hσ2, hθ, hθ2, hC₀, hC⟩, happ⟩

end QSH
