import QuantitativeStochasticHomogenization.Ch04.Sec04.CoordinateMinimizerCoercivity
import PDEFoundation.Measure.BallMaximalStrongNorm
import PDEFoundation.Analysis.Inequalities.Trudinger.CenteredMaximal

/-!
# Appendix D: the maximal function, Lemma D.4

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Appendix D, Lemma D.4: for `p ∈ (1, ∞]` and `f ∈ L^p(ℝ^d)`, the centered maximal function
`M f(x) = sup_{r > 0} ⨍_{B_r(x)} |f|` satisfies the strong `(p, p)`-type estimate (D.16),
`‖M f‖_{L^p(ℝ^d)} ≤ 2 (5^d p/(p - 1))^{1/p} ‖f‖_{L^p(ℝ^d)}`, where the constant is read as `2` for
`p = ∞` (`lemmaD4`).

For `p < ∞` the estimate follows from the strong estimate of the elliptic regularity library for the
uncentered maximal function over round balls, which dominates the centered one and satisfies the
estimate with the constant `2 (3^d p/(p - 1))^{1/p}` (`PDE.eLpNorm_uncenteredBallMaximal_le`, proved
there by a covering argument with the factor `3` in place of the factor `5` of Vitali's lemma). For
`p = ∞` every average is at most the essential supremum. The centered maximal function is lower
semicontinuous, hence measurable (`lowerSemicontinuous_maximalFunction`).
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

noncomputable section

namespace QSH

variable {d : ℕ}

/-- The centered maximal function `M f(x) = sup_{r > 0} ⨍_{B_r(x)} |f|` of Lemma D.4, with
extended values. -/
def maximalFunction (f : Vec d → ℝ) (x : Vec d) : ℝ≥0∞ :=
  ⨆ r : ℝ, ⨆ (_ : 0 < r), (volume (ball x r))⁻¹ * ∫⁻ y in ball x r, ‖f y‖ₑ

/-- The constant `2 (5^d p/(p - 1))^{1/p}` of (D.16), read as `2` for `p = ∞`. -/
def maximalConstant (d : ℕ) (p : ℝ≥0∞) : ℝ :=
  if p = ⊤ then 2 else 2 * ((5 : ℝ) ^ d * p.toReal / (p.toReal - 1)) ^ (1 / p.toReal)

theorem maximalFunction_eq_centeredBallMaximal (f : Vec d → ℝ) :
    maximalFunction f = PDE.Trudinger.centeredBallMaximal f := by
  funext x
  unfold maximalFunction PDE.Trudinger.centeredBallMaximal
  refine iSup_congr fun r => iSup_congr fun hr => ?_
  simp_rw [ball_eq_euclideanBall x hr, Real.enorm_eq_ofReal_abs]

/-- The integral of a function over the round ball `B_r(x)` is lower semicontinuous in the center. -/
theorem lowerSemicontinuous_setLIntegral_euclideanBall (g : Vec d → ℝ≥0∞) {r : ℝ} (hr : 0 < r) :
    LowerSemicontinuous fun x : Vec d => ∫⁻ y in PDE.euclideanBall x r, g y := by
  intro x c hc
  set s : ℕ → ℝ := fun n => r - r / ((n : ℝ) + 2) with hs
  have hgap : ∀ n : ℕ, 0 < r / ((n : ℝ) + 2) := fun n => div_pos hr (by positivity)
  have hs_pos : ∀ n, 0 < s n := fun n => by
    have : r / ((n : ℝ) + 2) < r := div_lt_self hr (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])
    simp only [hs]
    linarith
  have hs_mono : Monotone fun n => PDE.euclideanBall x (s n) := by
    intro m n hmn
    refine PDE.euclideanBall_mono (hs_pos m).le ?_
    have hmn' : (m : ℝ) + 2 ≤ (n : ℝ) + 2 := by
      have : (m : ℝ) ≤ n := by exact_mod_cast hmn
      linarith
    have : r / ((n : ℝ) + 2) ≤ r / ((m : ℝ) + 2) :=
      div_le_div_of_nonneg_left hr.le (by positivity) hmn'
    simp only [hs]
    linarith
  have hunion : (⋃ n, PDE.euclideanBall x (s n)) = PDE.euclideanBall x r := by
    ext z
    simp only [mem_iUnion]
    constructor
    · rintro ⟨n, hn⟩
      refine PDE.euclideanBall_mono (hs_pos n).le ?_ hn
      simp only [hs]
      linarith [hgap n]
    · intro hz
      rw [PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hr] at hz
      have hpos : 0 < r - PDE.vecEuclideanNorm (z - x) := by linarith
      obtain ⟨n, hn⟩ := exists_nat_gt (r / (r - PDE.vecEuclideanNorm (z - x)))
      refine ⟨n, ?_⟩
      rw [PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (hs_pos n)]
      have hlt : r / ((n : ℝ) + 2) < r - PDE.vecEuclideanNorm (z - x) := by
        rw [div_lt_iff₀ (by positivity)]
        rw [div_lt_iff₀ hpos] at hn
        nlinarith
      simp only [hs]
      linarith
  have hν : ∀ S : Set (Vec d), ∫⁻ y in S, g y = volume.withDensity g S := fun S =>
    (withDensity_apply' g S).symm
  change c < ∫⁻ y in PDE.euclideanBall x r, g y at hc
  rw [hν, ← hunion, hs_mono.measure_iUnion] at hc
  obtain ⟨n, hn⟩ := lt_iSup_iff.1 hc
  filter_upwards [(PDE.isOpen_euclideanBall x (r / ((n : ℝ) + 2))).mem_nhds
    (PDE.center_mem_euclideanBall x (hgap n))] with x' hx'
  show c < ∫⁻ y in PDE.euclideanBall x' r, g y
  rw [hν]
  refine hn.trans_le (measure_mono fun z hz => ?_)
  rw [PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (hgap n)] at hx'
  rw [PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (hs_pos n)] at hz
  rw [PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hr]
  have htri := PDE.vecEuclideanNorm_add_le (z - x) (x - x')
  rw [show z - x + (x - x') = z - x' by abel, PDE.vecEuclideanNorm_sub_comm x x'] at htri
  simp only [hs] at hz
  linarith

/-- The centered maximal function is lower semicontinuous. -/
theorem lowerSemicontinuous_maximalFunction (f : Vec d → ℝ) :
    LowerSemicontinuous (maximalFunction f) := by
  rw [maximalFunction_eq_centeredBallMaximal]
  unfold PDE.Trudinger.centeredBallMaximal
  refine lowerSemicontinuous_iSup fun r => lowerSemicontinuous_iSup fun hr => ?_
  have hv : ∀ x : Vec d,
      volume (PDE.euclideanBall x r) = volume (PDE.euclideanBall (0 : Vec d) r) := fun x => by
    rw [PDE.volume_euclideanBall_eq_unit_mul_of_pos x hr,
      PDE.volume_euclideanBall_eq_unit_mul_of_pos 0 hr]
  simp_rw [hv]
  exact (ENNReal.continuous_const_mul
    (ENNReal.inv_ne_top.2 (PDE.volume_euclideanBall_pos 0 hr).ne')).comp_lowerSemicontinuous
    (lowerSemicontinuous_setLIntegral_euclideanBall _ hr) fun a b hab => by dsimp only; gcongr

theorem measurable_maximalFunction (f : Vec d → ℝ) : Measurable (maximalFunction f) :=
  (lowerSemicontinuous_maximalFunction f).measurable

/-- The centered maximal function is dominated by the uncentered one. -/
theorem maximalFunction_le_uncenteredBallMaximal (f : Vec d → ℝ) (x : Vec d) :
    maximalFunction f x ≤ PDE.uncenteredBallMaximal f x := by
  rw [maximalFunction_eq_centeredBallMaximal]
  exact PDE.Trudinger.centeredBallMaximal_le_uncentered f x

/-- Every average of `|f|` over a ball is at most the essential supremum of `f`. -/
theorem maximalFunction_le_eLpNormEssSup (f : Vec d → ℝ) (x : Vec d) :
    maximalFunction f x ≤ eLpNormEssSup f volume := by
  refine iSup₂_le fun r hr => ?_
  have h0 : volume (ball x r) ≠ 0 := by
    rw [ball_eq_euclideanBall x hr]
    exact (PDE.volume_euclideanBall_pos x hr).ne'
  have htop : volume (ball x r) ≠ ⊤ := by
    rw [ball_eq_euclideanBall x hr]
    exact PDE.volume_euclideanBall_ne_top x hr.le
  calc (volume (ball x r))⁻¹ * ∫⁻ y in ball x r, ‖f y‖ₑ
      ≤ (volume (ball x r))⁻¹ * ∫⁻ _ in ball x r, eLpNormEssSup f volume :=
        mul_le_mul_of_nonneg_left
          (lintegral_mono_ae (ae_restrict_of_ae (ae_le_eLpNormEssSup (f := f)))) zero_le
    _ = eLpNormEssSup f volume := by
        rw [setLIntegral_const, mul_comm (eLpNormEssSup f volume), ← mul_assoc,
          ENNReal.inv_mul_cancel h0 htop, one_mul]

/-- The estimate (D.16) for a finite exponent `q ∈ (1, ∞)`. -/
theorem eLpNorm_maximalFunction_le {q : ℝ} (hq : 1 < q) {f : Vec d → ℝ}
    (hf : MemLp f (ENNReal.ofReal q) volume) :
    eLpNorm (maximalFunction f) (ENNReal.ofReal q) volume ≤
      ENNReal.ofReal (2 * ((5 : ℝ) ^ d * q / (q - 1)) ^ (1 / q)) *
        eLpNorm f (ENNReal.ofReal q) volume := by
  have hq0 : 0 < q := zero_lt_one.trans hq
  have hc : 2 * ((3 : ℝ) ^ d * q / (q - 1)) ^ (1 / q) ≤
      2 * ((5 : ℝ) ^ d * q / (q - 1)) ^ (1 / q) := by
    have h1 : (3 : ℝ) ^ d * q / (q - 1) ≤ (5 : ℝ) ^ d * q / (q - 1) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) (by norm_num) d) hq0.le)
        (sub_pos.2 hq).le
    have h2 : 0 ≤ (3 : ℝ) ^ d * q / (q - 1) := div_nonneg (by positivity) (sub_pos.2 hq).le
    have := Real.rpow_le_rpow h2 h1 (one_div_nonneg.2 hq0.le)
    linarith
  calc eLpNorm (maximalFunction f) (ENNReal.ofReal q) volume
      ≤ eLpNorm (PDE.uncenteredBallMaximal f) (ENNReal.ofReal q) volume :=
        eLpNorm_mono_enorm (measurable_maximalFunction f).aestronglyMeasurable fun x => by
          simpa only [enorm_eq_self] using maximalFunction_le_uncenteredBallMaximal f x
    _ ≤ ENNReal.ofReal (2 * ((3 : ℝ) ^ d * q / (q - 1)) ^ (1 / q)) *
          eLpNorm f (ENNReal.ofReal q) volume :=
        PDE.eLpNorm_uncenteredBallMaximal_le f hq hf
    _ ≤ _ := by gcongr

/-- **Lemma D.4.** For `p ∈ (1, ∞]` and `f ∈ L^p(ℝ^d)`, the maximal function satisfies the strong
`(p, p)`-type estimate (D.16), `‖M f‖_{L^p(ℝ^d)} ≤ 2 (5^d p/(p - 1))^{1/p} ‖f‖_{L^p(ℝ^d)}`, with
the constant read as `2` for `p = ∞`. -/
theorem lemmaD4 {p : ℝ≥0∞} (hp : 1 < p) {f : Vec d → ℝ} (hf : MemLp f p volume) :
    eLpNorm (maximalFunction f) p volume ≤
      ENNReal.ofReal (maximalConstant d p) * eLpNorm f p volume := by
  by_cases htop : p = ⊤
  · subst htop
    simp only [maximalConstant, ↓reduceIte]
    rw [eLpNorm_exponent_top (measurable_maximalFunction f).aestronglyMeasurable,
      eLpNorm_exponent_top hf.aestronglyMeasurable, ENNReal.ofReal_ofNat]
    calc eLpNormEssSup (maximalFunction f) volume ≤ eLpNormEssSup f volume :=
          eLpNormEssSup_le_of_ae_enorm_bound (Eventually.of_forall fun x => by
            simpa only [enorm_eq_self] using maximalFunction_le_eLpNormEssSup f x)
      _ ≤ 2 * eLpNormEssSup f volume := le_mul_of_one_le_left zero_le one_le_two
  · have hq : 1 < p.toReal := by
      have := (ENNReal.toReal_lt_toReal ENNReal.one_ne_top htop).2 hp
      simpa using this
    have hpq : ENNReal.ofReal p.toReal = p := ENNReal.ofReal_toReal htop
    simp only [maximalConstant, htop, ↓reduceIte]
    have := eLpNorm_maximalFunction_le hq (f := f) (by rw [hpq]; exact hf)
    rwa [hpq] at this

end QSH
