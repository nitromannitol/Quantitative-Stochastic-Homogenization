import QuantitativeStochasticHomogenization.Ch04.Sec03.ExpectedDensities
import QuantitativeStochasticHomogenization.Ch04.Sec01.EuclideanLipschitz

/-!
# The expectations (1) from Proposition 3.21 and stationarity

Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 4.3, the expectations (1) of the route of Proposition 4.10 (in the book, Lemma 3.23 and
(3.92)–(3.93)).

`expectedAveragesEstimate_of_energy_and_rate`: for a law satisfying the assumptions (0.10)–(0.11),
the energy bound below the scale (`GaussianEnergyBound`) and Proposition 3.21 at one exponent with
a positive rate (`GaussianCorrectorRate`) give `ExpectedAveragesEstimate P S β` for every `β > 0`.
The three densities `G ξ`, `a G ξ`, `G ξ · a G ξ` are stationary; their Gaussian averages are
dominated by `|ξ|(1 + C(1 + X^d))/2`, `Λ|ξ|(1 + C(1 + X^d))/2`, `C(1 + X^d)|ξ|²` (from
`|v| ≤ (t + t⁻¹ v·av)/2` at `t = |ξ|`), and by Proposition 3.21 their averages at the origin
converge almost surely to `ξ`, `āξ`, `ξ·āξ`. The expectation of each average is therefore within
the periodization error of these limits, and the periodization error is `O(r^{-β})` for every `β`.

`expectedAveragesEstimate_of_rate`: the same from Proposition 3.21 alone, the energy bound being
supplied by `gaussianEnergyBound_of_rate`.
-/

open MeasureTheory Filter Set
open scoped Topology

noncomputable section

namespace QSH

open BaseExponent

variable {d : ℕ} {Λ : ℝ}

/-! ## Envelopes -/

theorem eq_zero_of_euclideanNorm_eq_zero {ξ : Vec d} (h : euclideanNorm ξ = 0) : ξ = 0 := by
  have h2 : euclideanSq ξ = 0 := by
    rw [← euclideanNorm_sq, h]; ring
  unfold euclideanSq dot at h2
  funext i
  have := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => mul_self_nonneg (ξ j)).mp h2 i
    (Finset.mem_univ i)
  simpa using this

theorem euclideanNorm_le_half_add_inv_mul_energy (a : CoefficientField d Λ) {t : ℝ} (ht : 0 < t)
    (x v : Vec d) : euclideanNorm v ≤ (t + t⁻¹ * dot v ((a x).mulVec v)) / 2 := by
  set e := euclideanNorm v with hedef
  have h2 := (a.elliptic x v).1
  have h3 : e ^ 2 = euclideanSq v := euclideanNorm_sq v
  have h4 : 2 * t * e ≤ t ^ 2 + e ^ 2 := by nlinarith [sq_nonneg (t - e)]
  have h5 : e ≤ (t + t⁻¹ * e ^ 2) / 2 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
    have : t + t⁻¹ * e ^ 2 = (t ^ 2 + e ^ 2) / t := by field_simp
    rw [this, le_div_iff₀ ht]
    linarith
  have h6 : t⁻¹ * e ^ 2 ≤ t⁻¹ * dot v ((a x).mulVec v) :=
    mul_le_mul_of_nonneg_left (h3 ▸ h2) (inv_nonneg.mpr ht.le)
  linarith

theorem integral_heatKernel_mul_half_add (z : Vec d) {r : ℝ} (hr : 0 < r) (t : ℝ)
    {E : Vec d → ℝ} (hE : Integrable fun x => heatKernel z r x * E x) :
    Integrable (fun x => heatKernel z r x * ((t + t⁻¹ * E x) / 2)) ∧
      ∫ x, heatKernel z r x * ((t + t⁻¹ * E x) / 2) =
        (t + t⁻¹ * ∫ x, heatKernel z r x * E x) / 2 := by
  have hΦ := integrable_heatKernel z hr
  have he : (fun x => heatKernel z r x * ((t + t⁻¹ * E x) / 2)) =
      fun x => t / 2 * heatKernel z r x + t⁻¹ / 2 * (heatKernel z r x * E x) := by
    funext x; ring
  rw [he]
  refine ⟨(hΦ.const_mul _).add (hE.const_mul _), ?_⟩
  rw [integral_add (hΦ.const_mul _) (hE.const_mul _), integral_const_mul, integral_const_mul,
    integral_heatKernel z hr]
  ring

theorem correctedField_zero {P : Measure (CoefficientField d Λ)} (S : HomogenizationData P)
    (a : CoefficientField d Λ) (x : Vec d) : correctedField S a 0 x = 0 := by
  simp [correctedField]

section Envelopes

variable {P : Measure (CoefficientField d Λ)}

/-- **The envelopes of the gradient and flux averages**: if `∫ Φ_{z,r} Gξ·aGξ ≤ B |ξ|²`, then
`∫ Φ_{z,r} |Gξ| ≤ |ξ|(1 + B)/2` and `∫ Φ_{z,r} |aGξ| ≤ Λ|ξ|(1 + B)/2`. -/
theorem gradient_flux_envelope (hΛ : 0 ≤ Λ) (S : HomogenizationData P) (ξ : Vec d)
    (a : CoefficientField d Λ) (z : Vec d) {r : ℝ} (hr : 0 < r) {B : ℝ} (hB : 0 ≤ B)
    (hEi : Integrable fun x => heatKernel z r x *
      dot (correctedField S a ξ x) ((a x).mulVec (correctedField S a ξ x)))
    (hEb : ∫ x, heatKernel z r x *
      dot (correctedField S a ξ x) ((a x).mulVec (correctedField S a ξ x)) ≤ B * euclideanSq ξ) :
    (Integrable (fun x => heatKernel z r x * ‖correctedField S a ξ x‖) ∧
      ∫ x, heatKernel z r x * ‖correctedField S a ξ x‖ ≤ euclideanNorm ξ / 2 * (1 + B)) ∧
    (Integrable (fun x => heatKernel z r x * ‖fluxDensity S ξ a x‖) ∧
      ∫ x, heatKernel z r x * ‖fluxDensity S ξ a x‖ ≤ Λ * (euclideanNorm ξ / 2 * (1 + B))) := by
  have hGm : AEStronglyMeasurable (fun x => correctedField S a ξ x) volume :=
    ((measurable_correctedField S ξ).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  obtain ⟨h1, h2⟩ := integrable_averages_of_energy a hΛ z hr hGm hEi
  have hΦ0 := heatKernel_nonneg z r
  have hI1 : Integrable (fun x => heatKernel z r x * ‖correctedField S a ξ x‖) :=
    h1.norm.congr (Eventually.of_forall fun x => by
      simp only [norm_smul, Real.norm_of_nonneg (hΦ0 x)])
  have hI2 : Integrable (fun x => heatKernel z r x * ‖fluxDensity S ξ a x‖) :=
    h2.norm.congr (by
      filter_upwards [ae_fluxDensity_eq S ξ a] with x hx
      rw [hx, norm_smul, Real.norm_of_nonneg (hΦ0 x)])
  rcases eq_or_lt_of_le (euclideanNorm_nonneg ξ) with h0 | hpos
  · have hξ := eq_zero_of_euclideanNorm_eq_zero h0.symm
    rw [← h0]
    subst hξ
    simp [correctedField_zero, fluxDensity]
  set t := euclideanNorm ξ with htdef
  obtain ⟨hJ, hJe⟩ := integral_heatKernel_mul_half_add z hr t hEi
  have hmain : (t + t⁻¹ * ∫ x, heatKernel z r x *
      dot (correctedField S a ξ x) ((a x).mulVec (correctedField S a ξ x))) / 2 ≤ t / 2 * (1 + B) := by
    have h3 : t⁻¹ * (∫ x, heatKernel z r x *
        dot (correctedField S a ξ x) ((a x).mulVec (correctedField S a ξ x))) ≤
        t⁻¹ * (B * euclideanSq ξ) := mul_le_mul_of_nonneg_left hEb (inv_nonneg.mpr hpos.le)
    have h4 : t⁻¹ * (B * euclideanSq ξ) = B * t := by
      rw [← euclideanNorm_sq, ← htdef]; field_simp
    have h5 : (t + B * t) / 2 = t / 2 * (1 + B) := by ring
    linarith
  refine ⟨⟨hI1, ?_⟩, ⟨hI2, ?_⟩⟩
  · have hpt : ∀ x, heatKernel z r x * ‖correctedField S a ξ x‖ ≤ heatKernel z r x *
        ((t + t⁻¹ * dot (correctedField S a ξ x) ((a x).mulVec (correctedField S a ξ x))) / 2) :=
      fun x => mul_le_mul_of_nonneg_left ((norm_le_euclideanNorm _).trans
        (euclideanNorm_le_half_add_inv_mul_energy a hpos x _)) (hΦ0 x)
    exact (integral_mono hI1 hJ hpt).trans (hJe.le.trans hmain)
  · have hpt : ∀ᵐ x, heatKernel z r x * ‖fluxDensity S ξ a x‖ ≤ Λ * (heatKernel z r x *
        ((t + t⁻¹ * dot (correctedField S a ξ x) ((a x).mulVec (correctedField S a ξ x))) / 2)) := by
      filter_upwards [ae_fluxDensity_eq S ξ a] with x hx
      rw [hx]
      have h6 := (norm_le_euclideanNorm _).trans (euclideanNorm_coefficient_mulVec_le a hΛ x
        (correctedField S a ξ x))
      have h7 := euclideanNorm_le_half_add_inv_mul_energy a hpos x (correctedField S a ξ x)
      calc heatKernel z r x * ‖(a x).mulVec (correctedField S a ξ x)‖
          ≤ heatKernel z r x * (Λ * ((t + t⁻¹ * dot (correctedField S a ξ x)
            ((a x).mulVec (correctedField S a ξ x))) / 2)) :=
            mul_le_mul_of_nonneg_left (h6.trans (mul_le_mul_of_nonneg_left h7 hΛ)) (hΦ0 x)
        _ = _ := by ring
    calc ∫ x, heatKernel z r x * ‖fluxDensity S ξ a x‖
        ≤ ∫ x, Λ * (heatKernel z r x *
          ((t + t⁻¹ * dot (correctedField S a ξ x) ((a x).mulVec (correctedField S a ξ x))) / 2)) :=
          integral_mono_ae hI2 (hJ.const_mul Λ) hpt
      _ = Λ * ((t + t⁻¹ * ∫ x, heatKernel z r x *
          dot (correctedField S a ξ x) ((a x).mulVec (correctedField S a ξ x))) / 2) := by
          rw [integral_const_mul, hJe]
      _ ≤ Λ * (t / 2 * (1 + B)) := mul_le_mul_of_nonneg_left hmain hΛ

/-- **The envelope of the energy averages**: `∫ Φ_{z,r} |Gξ·aGξ| = ∫ Φ_{z,r} Gξ·aGξ`. -/
theorem energy_envelope (S : HomogenizationData P) (ξ : Vec d) (a : CoefficientField d Λ)
    (z : Vec d) (r : ℝ)
    (hEi : Integrable fun x => heatKernel z r x *
      dot (correctedField S a ξ x) ((a x).mulVec (correctedField S a ξ x))) :
    Integrable (fun x => heatKernel z r x * ‖energyDensity S ξ a x‖) ∧
      ∫ x, heatKernel z r x * ‖energyDensity S ξ a x‖ =
        ∫ x, heatKernel z r x *
          dot (correctedField S a ξ x) ((a x).mulVec (correctedField S a ξ x)) := by
  have he : (fun x => heatKernel z r x * ‖energyDensity S ξ a x‖) =ᵐ[volume] fun x =>
      heatKernel z r x * dot (correctedField S a ξ x) ((a x).mulVec (correctedField S a ξ x)) := by
    filter_upwards [ae_energyDensity_eq S ξ a] with x hx
    rw [hx, Real.norm_of_nonneg ((euclideanSq_nonneg _).trans (a.elliptic x _).1)]
  exact ⟨hEi.congr he.symm, integral_congr_ae he⟩

end Envelopes

/-! ## Almost sure limits from Proposition 3.21 -/

theorem tendsto_of_eventually_norm_sub_le {E : Type*} [SeminormedAddCommGroup E] {f : ℕ → E}
    {c : E} {b : ℕ → ℝ} (hb : Tendsto b atTop (𝓝 0)) (h : ∀ᶠ n in atTop, ‖f n - c‖ ≤ b n) :
    Tendsto f atTop (𝓝 c) :=
  tendsto_iff_norm_sub_tendsto_zero.mpr
    (squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) h hb)

theorem tendsto_const_mul_rpow_neg_nat (K : ℝ) {μ : ℝ} (hμ : 0 < μ) :
    Tendsto (fun n : ℕ => K * ((n : ℝ) + 1) ^ (-μ)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have h2 := ((tendsto_rpow_neg_atTop hμ).comp h1).const_mul K
  simpa using h2

theorem eventually_le_natCast_add_one (X : ℝ) : ∀ᶠ n : ℕ in atTop, X ≤ (n : ℝ) + 1 :=
  eventually_atTop.mpr ⟨⌈X⌉₊, fun n hn => by
    have h1 := Nat.le_ceil X
    have h2 : (⌈X⌉₊ : ℝ) ≤ n := by exact_mod_cast hn
    linarith⟩

/-- **Almost sure limits of the averages at the origin**, from Proposition 3.21 with a positive
rate. -/
theorem ae_tendsto_averages_of_rate {P : Measure (CoefficientField d Λ)} (S : HomogenizationData P)
    {τ C μ : ℝ} (hμ : 0 < μ) (hrate : GaussianCorrectorRate P S τ C μ) (ξ : Vec d) :
    ∀ᵐ a ∂P,
      Tendsto (fun n : ℕ => ∫ x, heatKernel 0 ((n : ℝ) + 1) x • correctedField S a ξ x) atTop
        (𝓝 ξ) ∧
      Tendsto (fun n : ℕ => ∫ x, heatKernel 0 ((n : ℝ) + 1) x • fluxDensity S ξ a x) atTop
        (𝓝 (S.homogenized.mulVec ξ)) ∧
      Tendsto (fun n : ℕ => ∫ x, heatKernel 0 ((n : ℝ) + 1) x • energyDensity S ξ a x) atTop
        (𝓝 (dot ξ (S.homogenized.mulVec ξ))) := by
  obtain ⟨X, -, hX⟩ := hrate
  filter_upwards [(hX 0).2] with a ha
  have hev : ∀ᶠ n : ℕ in atTop, GaussianAverageBounds a S.homogenized (correctedField S a) 0
      ((n : ℝ) + 1) (C * ((n : ℝ) + 1) ^ (-μ)) := by
    filter_upwards [eventually_le_natCast_add_one (X a 0)] with n hn
    exact ha _ (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith) hn
  refine ⟨?_, ?_, ?_⟩
  · refine tendsto_of_eventually_norm_sub_le (tendsto_const_mul_rpow_neg_nat
      (C * euclideanNorm ξ) hμ) ?_
    filter_upwards [hev] with n hn
    exact (norm_le_euclideanNorm _).trans ((hn ξ).2.2.2.1.trans (le_of_eq (by ring)))
  · refine tendsto_of_eventually_norm_sub_le (tendsto_const_mul_rpow_neg_nat
      (C * euclideanNorm ξ) hμ) ?_
    filter_upwards [hev] with n hn
    rw [integral_heatKernel_smul_fluxDensity]
    exact (norm_le_euclideanNorm _).trans ((hn ξ).2.2.2.2.1.trans (le_of_eq (by ring)))
  · refine tendsto_of_eventually_norm_sub_le (tendsto_const_mul_rpow_neg_nat
      (2 * C * euclideanNorm ξ ^ 2) hμ) ?_
    filter_upwards [hev] with n hn
    rw [integral_heatKernel_smul_energyDensity, Real.norm_eq_abs]
    exact (hn ξ).2.2.2.2.2.trans (le_of_eq (by ring))

end QSH
