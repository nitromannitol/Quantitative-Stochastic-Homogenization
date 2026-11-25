import QuantitativeStochasticHomogenization.Ch04.Sec03.ExpectedAveragesFromRate
import QuantitativeStochasticHomogenization.Ch04.Sec01.UniformGaussianRate
import QuantitativeStochasticHomogenization.Ch04.Sec06.NegativeSobolevSublinear

/-!
# Lemma 3.23: the expectations of the Gaussian averages of the corrected fields

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 3.4, Lemma 3.23 (`lemma_3_23`): there are `c(d, Λ) > 0` and `C(d, Λ) < ∞` such that, for
every `e ∈ ∂B₁`, `x ∈ ℝ^d` and `r ≥ 1`, the expectations of the Gaussian averages
`∫ Φ_{x,r} ∇φ_e`, `∫ Φ_{x,r} (a(e + ∇φ_e) - āe)` and
`∫ Φ_{x,r} (½ (e + ∇φ_e)·a(e + ∇φ_e) - ½ e·āe)` are at most `C exp(-c r²)`, (3.106)–(3.108).

The densities are stationary, so their expectations are lattice periodic, and the Gaussian average
of a periodic function is within the periodization error of its cell mean
(`expectedAveragesBounds_of_energy_and_rate`); the periodization error of `Φ_{x,r}` is at most
`C exp(-4π² r²)` (`periodizationError_le_exp`), which is (3.109) for the heat kernel. The cell
means are identified by Proposition 3.21 (`uniformGaussianCorrectorRate`), whose constants are
chosen before the law.
-/

open MeasureTheory Filter Set

noncomputable section

namespace QSH

open BaseExponent

variable {d : ℕ} {Λ : ℝ}

/-- **The periodization error at scale `r ≥ 1` is at most `C exp(-4π² r²)`.** -/
theorem periodizationError_le_exp :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 1 ≤ r →
      (1 + thetaError (r ^ 2)) ^ d - 1 ≤ C * Real.exp (-(4 * Real.pi ^ 2 * r ^ 2)) := by
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = (d : ℝ) * (1 + thetaError 1) ^ d * thetaError 1 := ⟨_, rfl⟩
  have hE1 := thetaError_nonneg (t := 1) one_pos
  have hK0 : 0 ≤ K := by
    rw [hK]
    positivity
  refine ⟨(K + 1) * Real.exp (4 * Real.pi ^ 2), by positivity, fun r hr => ?_⟩
  have h := periodizationError_le (d := d) hr
  rw [← hK] at h
  have e : Real.exp (-(4 * Real.pi ^ 2 * (r ^ 2 - 1))) =
      Real.exp (4 * Real.pi ^ 2) * Real.exp (-(4 * Real.pi ^ 2 * r ^ 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [e] at h
  have hx : 0 ≤ Real.exp (4 * Real.pi ^ 2) * Real.exp (-(4 * Real.pi ^ 2 * r ^ 2)) := by
    positivity
  linarith

/-- **Lemma 3.23**: for `d ≥ 2` and `Λ > 1` there are `c > 0` and `C < ∞`, chosen before the law,
such that every law satisfying the assumptions has homogenization data (those of
Proposition 3.21) with the following property. For every `x ∈ ℝ^d`, `r ≥ 1` and `e ∈ ∂B₁`, writing
`∇φ_e = G e - e` for the corrected field `G e = ∑ᵢ eᵢ (eᵢ + ∇φ_{eᵢ})`, the Gaussian averages of
`∇φ_e`, `a(e + ∇φ_e) - āe` and `½ (e + ∇φ_e)·a(e + ∇φ_e) - ½ e·āe` against `Φ_{x,r}` are almost
surely integrals of integrable functions, they are integrable in the coefficient field, and their
expectations are at most `C exp(-c r²)` in norm, (3.106)–(3.108). -/
theorem lemma_3_23 (hd : 2 ≤ d) (hΛ : 1 < Λ) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ P : Measure (CoefficientField d Λ), LawHypotheses P →
      ∃ S : HomogenizationData P, ∀ (x : Vec d) (r : ℝ), 1 ≤ r → ∀ e : Vec d,
        euclideanNorm e = 1 →
        (∀ᵐ a ∂P, Integrable (fun y => heatKernel x r y • (correctedField S a e y - e)) ∧
          Integrable (fun y => heatKernel x r y •
            ((a y).mulVec (correctedField S a e y) - S.homogenized.mulVec e)) ∧
          Integrable (fun y => heatKernel x r y *
            ((1 / 2) * dot (correctedField S a e y) ((a y).mulVec (correctedField S a e y)) -
              (1 / 2) * dot e (S.homogenized.mulVec e)))) ∧
        Integrable (fun a => ∫ y, heatKernel x r y • (correctedField S a e y - e)) P ∧
        Integrable (fun a => ∫ y, heatKernel x r y •
          ((a y).mulVec (correctedField S a e y) - S.homogenized.mulVec e)) P ∧
        Integrable (fun a => ∫ y, heatKernel x r y *
          ((1 / 2) * dot (correctedField S a e y) ((a y).mulVec (correctedField S a e y)) -
            (1 / 2) * dot e (S.homogenized.mulVec e))) P ∧
        euclideanNorm (∫ a, (∫ y, heatKernel x r y • (correctedField S a e y - e)) ∂P) ≤
          C * Real.exp (-(c * r ^ 2)) ∧
        euclideanNorm (∫ a, (∫ y, heatKernel x r y •
          ((a y).mulVec (correctedField S a e y) - S.homogenized.mulVec e)) ∂P) ≤
          C * Real.exp (-(c * r ^ 2)) ∧
        |∫ a, (∫ y, heatKernel x r y *
          ((1 / 2) * dot (correctedField S a e y) ((a y).mulVec (correctedField S a e y)) -
            (1 / 2) * dot e (S.homogenized.mulVec e))) ∂P| ≤
          C * Real.exp (-(c * r ^ 2)) := by
  obtain ⟨Cr, μr, hCμ, hrate⟩ := uniformGaussianCorrectorRate d hd Λ hΛ
  have hd0 : 0 < d := by omega
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have h1d : (1 : ℝ) < d := by linarith
  have hΛ0 : 0 ≤ Λ := by linarith
  obtain ⟨hC1, hμ1⟩ := hCμ 1 one_pos h1d
  obtain ⟨Cβ, hCβ, hCβb⟩ := periodizationError_le_exp (d := d)
  obtain ⟨CN, hCN⟩ : ∃ CN : ℝ, CN = gaussianRateEnergyScale 1 (Cr 1) Λ := ⟨_, rfl⟩
  have hCN0 : 0 < CN := by
    rw [hCN]
    exact lt_max_of_lt_left (mul_pos (Real.rpow_pos_of_pos two_pos _) (lt_max_of_lt_left hC1))
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = ((d : ℝ) + 1) * Cβ * (cellHeatLower d)⁻¹ * (Λ + 1) *
      (1 + CN * (1 + momentConstant (1 / d) * CN ^ (d : ℝ))) := ⟨_, rfl⟩
  have hc0 : 0 < (cellHeatLower d)⁻¹ := inv_pos.mpr (cellHeatLower_pos d)
  have hm : 0 ≤ momentConstant (1 / d) * CN ^ (d : ℝ) :=
    mul_nonneg (momentConstant_pos _).le (Real.rpow_nonneg hCN0.le _)
  have hK0 : 0 < K := by
    rw [hK]
    positivity
  refine ⟨4 * Real.pi ^ 2, K, by positivity, hK0, fun P hP => ?_⟩
  have := hP.1
  obtain ⟨S, hS⟩ := hrate P hP
  have hA := S.homogenizedMatrixBounds hΛ0
  have hN := (gaussianEnergyBound_of_rate_at S (fun ξ => (hA ξ).2) one_pos hμ1.le
    (hS 1 one_pos h1d)).2
  have hB := expectedAveragesBounds_of_energy_and_rate hd0 hP S hΛ0 hN hμ1 (hS 1 one_pos h1d)
    (fun r => 4 * Real.pi ^ 2 * r ^ 2) hCβ hCβb
  have hI := averagesIntegrable_of_lawHypotheses hd hΛ hP S
  refine ⟨S, fun x r hr e he => ?_⟩
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hΦ := integrable_heatKernel x hr0
  have hΦ1 := integral_heatKernel x hr0
  obtain ⟨hIG, hIF, hIW, hbG, hbF, hbW⟩ := hB x r hr e
  rw [← hCN] at hbG hbF hbW
  rw [← hK] at hbG hbF hbW
  have he2 : euclideanSq e = 1 := by rw [← euclideanNorm_sq, he, one_pow]
  rw [he, mul_one] at hbG hbF
  rw [he2, mul_one] at hbW
  have hε0 : 0 ≤ Real.exp (-(4 * Real.pi ^ 2 * r ^ 2)) := (Real.exp_pos _).le
  have hae : ∀ᵐ a ∂P,
      Integrable (fun y => heatKernel x r y • (correctedField S a e y - e)) ∧
      Integrable (fun y => heatKernel x r y •
        ((a y).mulVec (correctedField S a e y) - S.homogenized.mulVec e)) ∧
      Integrable (fun y => heatKernel x r y *
        ((1 / 2) * dot (correctedField S a e y) ((a y).mulVec (correctedField S a e y)) -
          (1 / 2) * dot e (S.homogenized.mulVec e))) ∧
      ∫ y, heatKernel x r y • (correctedField S a e y - e) =
        (∫ y, heatKernel x r y • correctedField S a e y) - e ∧
      ∫ y, heatKernel x r y • ((a y).mulVec (correctedField S a e y) - S.homogenized.mulVec e) =
        (∫ y, heatKernel x r y • (a y).mulVec (correctedField S a e y)) -
          S.homogenized.mulVec e ∧
      ∫ y, heatKernel x r y *
          ((1 / 2) * dot (correctedField S a e y) ((a y).mulVec (correctedField S a e y)) -
            (1 / 2) * dot e (S.homogenized.mulVec e)) =
        (1 / 2) * (∫ y, heatKernel x r y *
          dot (correctedField S a e y) ((a y).mulVec (correctedField S a e y))) -
          (1 / 2) * dot e (S.homogenized.mulVec e) := by
    filter_upwards [hI x] with a ha
    obtain ⟨h1, h2, h3⟩ := ha r hr e
    have hc1 : Integrable (fun y => heatKernel x r y • e) := hΦ.smul_const e
    have hc2 : Integrable (fun y => heatKernel x r y • S.homogenized.mulVec e) :=
      hΦ.smul_const _
    have hc3 : Integrable (fun y => (1 / 2) * dot e (S.homogenized.mulVec e) * heatKernel x r y) :=
      hΦ.const_mul _
    have e1 : (fun y => heatKernel x r y • (correctedField S a e y - e)) =
        fun y => heatKernel x r y • correctedField S a e y - heatKernel x r y • e := by
      funext y
      rw [smul_sub]
    have e2 : (fun y => heatKernel x r y •
          ((a y).mulVec (correctedField S a e y) - S.homogenized.mulVec e)) =
        fun y => heatKernel x r y • (a y).mulVec (correctedField S a e y) -
          heatKernel x r y • S.homogenized.mulVec e := by
      funext y
      rw [smul_sub]
    have e3 : (fun y => heatKernel x r y *
          ((1 / 2) * dot (correctedField S a e y) ((a y).mulVec (correctedField S a e y)) -
            (1 / 2) * dot e (S.homogenized.mulVec e))) =
        fun y => (1 / 2) * (heatKernel x r y *
          dot (correctedField S a e y) ((a y).mulVec (correctedField S a e y))) -
          (1 / 2) * dot e (S.homogenized.mulVec e) * heatKernel x r y := by
      funext y
      ring
    have hs1 : ∫ y, heatKernel x r y • e = e := by
      rw [integral_smul_const, hΦ1, one_smul]
    have hs2 : ∫ y, heatKernel x r y • S.homogenized.mulVec e = S.homogenized.mulVec e := by
      rw [integral_smul_const, hΦ1, one_smul]
    have hs3 : ∫ y, (1 / 2) * dot e (S.homogenized.mulVec e) * heatKernel x r y =
        (1 / 2) * dot e (S.homogenized.mulVec e) := by
      rw [integral_const_mul, hΦ1, mul_one]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [e1]
      exact h1.sub hc1
    · rw [e2]
      exact h2.sub hc2
    · rw [e3]
      exact (h3.const_mul _).sub hc3
    · rw [e1, integral_sub h1 hc1, hs1]
    · rw [e2, integral_sub h2 hc2, hs2]
    · rw [e3, integral_sub (h3.const_mul _) hc3, integral_const_mul, hs3]
  have hcG : (fun a => ∫ y, heatKernel x r y • (correctedField S a e y - e)) =ᵐ[P]
      fun a => (∫ y, heatKernel x r y • correctedField S a e y) - e := by
    filter_upwards [hae] with a ha
    exact ha.2.2.2.1
  have hcF : (fun a => ∫ y, heatKernel x r y •
        ((a y).mulVec (correctedField S a e y) - S.homogenized.mulVec e)) =ᵐ[P]
      fun a => (∫ y, heatKernel x r y • (a y).mulVec (correctedField S a e y)) -
        S.homogenized.mulVec e := by
    filter_upwards [hae] with a ha
    exact ha.2.2.2.2.1
  have hcW : (fun a => ∫ y, heatKernel x r y *
        ((1 / 2) * dot (correctedField S a e y) ((a y).mulVec (correctedField S a e y)) -
          (1 / 2) * dot e (S.homogenized.mulVec e))) =ᵐ[P]
      fun a => (1 / 2) * (∫ y, heatKernel x r y *
        dot (correctedField S a e y) ((a y).mulVec (correctedField S a e y))) -
          (1 / 2) * dot e (S.homogenized.mulVec e) := by
    filter_upwards [hae] with a ha
    exact ha.2.2.2.2.2
  have hiG := hIG.sub (integrable_const e)
  have hiF := hIF.sub (integrable_const (S.homogenized.mulVec e))
  have hiW := (hIW.const_mul (1 / 2)).sub
    (integrable_const ((1 / 2) * dot e (S.homogenized.mulVec e)))
  refine ⟨hae.mono fun a ha => ⟨ha.1, ha.2.1, ha.2.2.1⟩, hiG.congr hcG.symm,
    hiF.congr hcF.symm, hiW.congr hcW.symm, ?_, ?_, ?_⟩
  · rw [integral_congr_ae hcG, integral_sub hIG (integrable_const e), integral_const,
      probReal_univ, one_smul]
    exact hbG
  · rw [integral_congr_ae hcF, integral_sub hIF (integrable_const _), integral_const,
      probReal_univ, one_smul]
    exact hbF
  · rw [integral_congr_ae hcW, integral_sub (hIW.const_mul _) (integrable_const _),
      integral_const, probReal_univ, one_smul, integral_const_mul, ← mul_sub, abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have hKε : 0 ≤ K * Real.exp (-(4 * Real.pi ^ 2 * r ^ 2)) := mul_nonneg hK0.le hε0
    linarith

end QSH
