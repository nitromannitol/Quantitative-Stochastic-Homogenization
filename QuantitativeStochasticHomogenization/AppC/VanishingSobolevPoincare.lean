import QuantitativeStochasticHomogenization.AppC.GlobalCaccioppoliLemma
import PDEFoundation.Sobolev.H1.ZeroExtension

/-!
# The Sobolev–Poincaré inequality for functions vanishing on a set of positive measure

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Appendix C, proof of Corollary C.9: for `u ∈ H¹₀(U)` extended by zero and a ball `B_ρ(y)` with
`|B_ρ(y) \ U| ≥ θ |B_ρ|`, `‖u‖_{L̲²(B_ρ(y))} ≤ C(d, θ) ρ ‖∇u‖_{L̲^{2_*}(B_ρ(y))}` (the book cites
[79, Lemma 4.8]). The proof is the standard one: for any constant `m`,
`|m| θ^{1/2} ≤ ‖w - m‖_{L̲²(B)}` when `w = 0` on a set of measure `θ |B|`, so
`‖w‖_{L̲²(B)} ≤ (1 + θ^{-1/2}) ‖w - m‖_{L̲²(B)}`, and the mean-zero Sobolev–Poincaré inequality on
convex domains of the elliptic regularity library (`PDE.exists_convexSobolevPoincare_constant`,
with `p = 2_*` and `p^* = 2`) applies to `m = (w)_B`. The zero extension of `u` is an `H¹`
function on `ℝ^d` (`PDE.H10Function.zeroExtendToH1`).
-/

open MeasureTheory Filter Set
open scoped ENNReal Topology

noncomputable section

namespace QSH

variable {d : ℕ}

/-- If `w = 0` on `E ⊆ B` with `|E| ≥ θ |B|`, then for every constant `m`,
`‖w‖_{L̲²(B)} ≤ (1 + θ^{-1/2}) ‖w - m‖_{L̲²(B)}`. -/
theorem eLpMeanNormOn_two_le_of_eq_zero_on {B E : Set (Vec d)} (hB0 : volume B ≠ 0)
    (hBt : volume B ≠ ⊤) (hEB : E ⊆ B) (hEm : MeasurableSet E) {θ : ℝ} (hθ : 0 < θ)
    (hE : θ * volume.real B ≤ volume.real E) {w : Vec d → ℝ}
    (hw : MemLp w 2 (volume.restrict B)) (hw0 : ∀ x ∈ E, w x = 0) (m : ℝ) :
    PDE.eLpMeanNormOn B 2 w ≤
      ENNReal.ofReal (1 + θ ^ (-(1 : ℝ) / 2)) * PDE.eLpMeanNormOn B 2 (fun x => w x - m) := by
  set μ := PDE.normalizedVolumeOn B with hμ
  have hpos : 0 < volume B := pos_iff_ne_zero.mpr hB0
  have : IsProbabilityMeasure μ :=
    PDE.isProbabilityMeasure_normalizedVolumeOn_of_pos_of_lt_top hpos hBt.lt_top
  have : IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.mpr hBt
  have hwm : MemLp (fun x => w x - m) 2 (volume.restrict B) := hw.sub (memLp_const m)
  have hvB : 0 < volume.real B := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos hB0 hBt
  -- the triangle inequality
  have h1 : PDE.eLpMeanNormOn B 2 w ≤
      PDE.eLpMeanNormOn B 2 (fun x => w x - m) + ENNReal.ofReal |m| := by
    have e : w = (fun x => w x - m) + fun _ => m := by
      funext x
      simp
    have hc : eLpNorm (fun _ : Vec d => m) 2 μ = ENNReal.ofReal |m| := by
      rw [eLpNorm_const _ two_ne_zero (IsProbabilityMeasure.ne_zero μ), measure_univ,
        ENNReal.one_rpow, mul_one, Real.enorm_eq_ofReal_abs]
    calc PDE.eLpMeanNormOn B 2 w = eLpNorm ((fun x => w x - m) + fun _ => m) 2 μ := by
          rw [← e]
          rfl
      _ ≤ eLpNorm (fun x => w x - m) 2 μ + eLpNorm (fun _ : Vec d => m) 2 μ :=
          eLpNorm_add_le (by norm_num)
      _ = PDE.eLpMeanNormOn B 2 (fun x => w x - m) + ENNReal.ofReal |m| := by
          rw [hc]
          rfl
  -- the constant is controlled on the zero set
  have h2 : |m| ≤ θ ^ (-(1 : ℝ) / 2) * scalarRms volume B (fun x => w x - m) := by
    have hint : IntegrableOn (fun x => (w x - m) ^ 2) B := hwm.integrable_sq
    have hlow : θ * m ^ 2 ≤ ⨍ x in B, (w x - m) ^ 2 ∂volume := by
      rw [setAverage_eq, smul_eq_mul]
      have hE' : ∫ x in E, (w x - m) ^ 2 = volume.real E * m ^ 2 := by
        rw [setIntegral_congr_fun hEm (g := fun _ => m ^ 2) fun x hx => by
          simp only [hw0 x hx, zero_sub, neg_sq], setIntegral_const, smul_eq_mul]
      have hEB' : ∫ x in E, (w x - m) ^ 2 ≤ ∫ x in B, (w x - m) ^ 2 :=
        setIntegral_mono_set hint (Eventually.of_forall fun x => sq_nonneg _)
          (Eventually.of_forall hEB)
      rw [hE'] at hEB'
      rw [le_inv_mul_iff₀ hvB]
      nlinarith [sq_nonneg m]
    have hθs : θ ^ (-(1 : ℝ) / 2) * Real.sqrt θ = 1 := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hθ]
      norm_num
    have hs : Real.sqrt θ * |m| ≤ scalarRms volume B (fun x => w x - m) := by
      rw [scalarRms, ← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul hθ.le]
      exact Real.sqrt_le_sqrt hlow
    calc |m| = θ ^ (-(1 : ℝ) / 2) * (Real.sqrt θ * |m|) := by rw [← mul_assoc, hθs, one_mul]
      _ ≤ θ ^ (-(1 : ℝ) / 2) * scalarRms volume B (fun x => w x - m) :=
          mul_le_mul_of_nonneg_left hs (Real.rpow_nonneg hθ.le _)
  have e3 := eLpMeanNormOn_two_eq_ofReal_scalarRms hB0 hwm
  have hθ0 : 0 ≤ θ ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg hθ.le _
  calc PDE.eLpMeanNormOn B 2 w
      ≤ PDE.eLpMeanNormOn B 2 (fun x => w x - m) + ENNReal.ofReal |m| := h1
    _ ≤ PDE.eLpMeanNormOn B 2 (fun x => w x - m) +
          ENNReal.ofReal (θ ^ (-(1 : ℝ) / 2)) * PDE.eLpMeanNormOn B 2 (fun x => w x - m) := by
        gcongr
        rw [e3, ← ENNReal.ofReal_mul hθ0]
        exact ENNReal.ofReal_le_ofReal h2
    _ = ENNReal.ofReal (1 + θ ^ (-(1 : ℝ) / 2)) * PDE.eLpMeanNormOn B 2 (fun x => w x - m) := by
        rw [ENNReal.ofReal_add zero_le_one hθ0, ENNReal.ofReal_one, add_mul, one_mul]

/-- **The Sobolev–Poincaré inequality for `H¹₀(U)` functions on balls with a large zero set**
(the input [79, Lemma 4.8] of Corollary C.9). For `d ≥ 2` there is `C(d)` such that, for an open
`U`, `u ∈ H¹₀(U)` extended by zero, a ball `B_ρ(y)` and `θ > 0` with
`|B_ρ(y) \ U| ≥ θ |B_ρ(y)|`,
`‖u‖_{L̲²(B_ρ(y))} ≤ (1 + θ^{-1/2}) C ρ ‖∇u‖_{L̲^{2_*}(B_ρ(y))}`, `2_* = 2d/(d+2)`. -/
theorem sobolevPoincare_of_vanishing (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (U : Set (Vec d)), IsOpen U → ∀ (u : Vec d → ℝ) (g : Vec d → Vec d),
      H01 U u g → ∀ (y : Vec d) (ρ : ℝ), 0 < ρ → ∀ θ : ℝ, 0 < θ →
      θ * volume.real (ball y ρ) ≤ volume.real (ball y ρ \ U) →
      PDE.eLpMeanNormOn (ball y ρ) 2 (U.indicator u) ≤
        ENNReal.ofReal ((1 + θ ^ (-(1 : ℝ) / 2)) * C * ρ) *
          PDE.eLpMeanNormOn (ball y ρ) (ENNReal.ofReal (2 * d / (d + 2)))
            (fun x => euclideanNorm (U.indicator g x)) := by
  obtain ⟨Cs, hCs, hsp⟩ := PDE.exists_convexSobolevPoincare_constant d hd
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨p, hpdef⟩ : ∃ p : ℝ, p = 2 * d / (d + 2) := ⟨_, rfl⟩
  have hp1 : 1 ≤ p := by
    rw [hpdef, le_div_iff₀ (by linarith)]
    linarith
  have hpd : p < d := by
    rw [hpdef, div_lt_iff₀ (by linarith)]
    nlinarith
  have hp2 : p ≤ 2 := by
    rw [hpdef, div_le_iff₀ (by linarith)]
    linarith
  have hconj : PDE.sobolevConjugate d p = 2 := by
    rw [PDE.sobolevConjugate, hpdef]
    have h1 : (d : ℝ) + 2 ≠ 0 := by linarith
    have h2 : (d : ℝ) - 2 * d / (d + 2) = d ^ 2 / (d + 2) := by
      field_simp
      ring
    rw [h2]
    have h3 : (d : ℝ) ^ 2 ≠ 0 := by positivity
    field_simp
  obtain ⟨k, hkdef⟩ : ∃ k : ℝ, k = p * ((d : ℝ) - 1) / ((d : ℝ) - p) := ⟨_, rfl⟩
  have hk : 0 ≤ k := by
    rw [hkdef]
    exact div_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  refine ⟨2 * Cs * k + 1, by positivity, ?_⟩
  intro U hUo u g hu y ρ hρ θ hθ hθB
  set B := ball y ρ with hBdef
  have hBe : B = PDE.euclideanBall y ρ := ball_eq_euclideanBall y hρ
  have hconv : PDE.IsOpenBoundedConvexDomain B := by
    rw [hBe]
    exact PDE.isOpenBoundedConvexDomain_euclideanBall y hρ
  have hB0 : volume B ≠ 0 := by
    rw [hBe]
    exact (PDE.volume_euclideanBall_pos y hρ).ne'
  have hBt : volume B ≠ ⊤ := by
    rw [hBe]
    exact PDE.volume_euclideanBall_ne_top y hρ.le
  have : IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.mpr hBt
  have hne : B.Nonempty := by
    rw [hBe]
    exact PDE.euclideanBall_nonempty y hρ
  have hdiam : PDE.HasEuclideanDiameterLE B (2 * ρ) := by
    rw [hBe]
    exact PDE.hasEuclideanDiameterLE_euclideanBall y hρ
  -- the zero extension of `u`, restricted to `B`
  set w : PDE.H1Function B := (hu.toH10Function.zeroExtendToH1 isOpen_univ hUo
    (subset_univ U)).restrict hconv.isOpen (subset_univ B) with hwdef
  have hwf : w.toFun = U.indicator u := rfl
  have hwg : w.grad = U.indicator g := rfl
  have hp2' : ENNReal.ofReal p ≤ 2 := by
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp]
    exact ENNReal.ofReal_le_ofReal hp2
  let uw : PDE.W1pFunction B (ENNReal.ofReal p) :=
    { toFun := w.toFun
      grad := w.grad
      memLp := w.memL2.mono_exponent hp2'
      gradMemLp := fun i => (w.gradMemL2 i).mono_exponent hp2'
      hasWeakGradient := w.hasWeakGradient }
  have hs := hsp p hp1 hpd B (2 * ρ) hconv hne hdiam uw
  rw [hconj, ENNReal.ofReal_ofNat, ← hkdef] at hs
  set N := PDE.eLpMeanNormOn B (ENNReal.ofReal (2 * d / (d + 2)))
    (fun x => euclideanNorm (U.indicator g x)) with hNdef
  have hsN : PDE.eLpMeanNormOn B 2 (fun x => w.toFun x - PDE.integralAverage B w.toFun) ≤
      ENNReal.ofReal (Cs * k * (2 * ρ)) * N := by
    rw [hNdef, ← hpdef]
    exact hs
  -- the zero set
  have hEm : MeasurableSet (B \ U) := hconv.isOpen.measurableSet.diff hUo.measurableSet
  have hw0 : ∀ x ∈ B \ U, w.toFun x = 0 := fun x hx => by
    rw [hwf]
    exact indicator_of_notMem hx.2 _
  have hvan := eLpMeanNormOn_two_le_of_eq_zero_on hB0 hBt sdiff_subset hEm hθ hθB w.memL2 hw0
    (PDE.integralAverage B w.toFun)
  have hθ0 : 0 ≤ 1 + θ ^ (-(1 : ℝ) / 2) := by
    have := Real.rpow_nonneg hθ.le (-(1 : ℝ) / 2)
    linarith
  change PDE.eLpMeanNormOn B 2 w.toFun ≤ _
  calc PDE.eLpMeanNormOn B 2 w.toFun
      ≤ ENNReal.ofReal (1 + θ ^ (-(1 : ℝ) / 2)) *
          PDE.eLpMeanNormOn B 2 (fun x => w.toFun x - PDE.integralAverage B w.toFun) := hvan
    _ ≤ ENNReal.ofReal (1 + θ ^ (-(1 : ℝ) / 2)) * (ENNReal.ofReal (Cs * k * (2 * ρ)) * N) := by
        gcongr
    _ = ENNReal.ofReal ((1 + θ ^ (-(1 : ℝ) / 2)) * (Cs * k * (2 * ρ))) * N := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hθ0]
    _ ≤ ENNReal.ofReal ((1 + θ ^ (-(1 : ℝ) / 2)) * (2 * Cs * k + 1) * ρ) * N := by
        gcongr ENNReal.ofReal ?_ * _
        nlinarith [mul_nonneg hθ0 hρ.le]

end QSH
